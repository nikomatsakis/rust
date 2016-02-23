// Copyright 2012-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
//! Declare various LLVM values.
//!
//! Prefer using functions and methods from this module rather than calling LLVM
//! functions directly. These functions do some additional work to ensure we do
//! the right thing given the preconceptions of trans.
//!
//! Some useful guidelines:
//!
//! * Use declare_* family of methods if you are declaring, but are not
//!   interested in defining the ValueRef they return.
//! * Use define_* family of methods when you might be defining the ValueRef.
//! * When in doubt, define.
use llvm::{self, ValueRef};
use middle::ty;
use middle::infer;
use syntax::abi::Abi;
use trans::attributes;
use trans::base;
use trans::cabi::FnType;
use trans::context::CrateContext;
use trans::type_::Type;
use trans::type_of;

use std::ffi::CString;
use libc::c_uint;


/// Declare a global value.
///
/// If there’s a value with the same name already declared, the function will
/// return its ValueRef instead.
pub fn declare_global(ccx: &CrateContext, name: &str, ty: Type) -> llvm::ValueRef {
    debug!("declare_global(name={:?})", name);
    let namebuf = CString::new(name).unwrap_or_else(|_|{
        ccx.sess().bug(&format!("name {:?} contains an interior null byte", name))
    });
    unsafe {
        llvm::LLVMGetOrInsertGlobal(ccx.llmod(), namebuf.as_ptr(), ty.to_ref())
    }
}


/// Declare a function.
///
/// If there’s a value with the same name already declared, the function will
/// update the declaration and return existing ValueRef instead.
fn declare_raw_fn(ccx: &CrateContext, name: &str, callconv: llvm::CallConv, ty: Type) -> ValueRef {
    debug!("declare_raw_fn(name={:?}, ty={:?})", name, ty);
    let namebuf = CString::new(name).unwrap_or_else(|_|{
        ccx.sess().bug(&format!("name {:?} contains an interior null byte", name))
    });
    let llfn = unsafe {
        llvm::LLVMGetOrInsertFunction(ccx.llmod(), namebuf.as_ptr(), ty.to_ref())
    };

    llvm::SetFunctionCallConv(llfn, callconv);
    // Function addresses in Rust are never significant, allowing functions to
    // be merged.
    llvm::SetUnnamedAddr(llfn, true);

    if ccx.tcx().sess.opts.cg.no_redzone
        .unwrap_or(ccx.tcx().sess.target.target.options.disable_redzone) {
        llvm::SetFunctionAttribute(llfn, llvm::Attribute::NoRedZone)
    }

    llfn
}


/// Declare a C ABI function.
///
/// Only use this for foreign function ABIs and glue. For Rust functions use
/// `declare_fn` instead.
///
/// If there’s a value with the same name already declared, the function will
/// update the declaration and return existing ValueRef instead.
pub fn declare_cfn(ccx: &CrateContext, name: &str, fn_type: Type) -> ValueRef {
    declare_raw_fn(ccx, name, llvm::CCallConv, fn_type)
}


/// Declare a Rust function.
///
/// If there’s a value with the same name already declared, the function will
/// update the declaration and return existing ValueRef instead.
pub fn declare_fn<'a, 'tcx>(ccx: &CrateContext<'a, 'tcx>, name: &str,
                            fn_type: ty::Ty<'tcx>) -> ValueRef {
    debug!("declare_rust_fn(name={:?}, fn_type={:?})", name,
           fn_type);

    let function_type; // placeholder so that the memory ownership works out ok
    let (sig, abi, env) = match fn_type.sty {
        ty::TyFnDef(_, _, f) |
        ty::TyFnPtr(f) => {
            (&f.sig, f.abi, None)
        }
        ty::TyClosure(closure_did, ref substs) => {
            let infcx = infer::normalizing_infer_ctxt(ccx.tcx(), &ccx.tcx().tables);
            function_type = infcx.closure_type(closure_did, substs);
            let self_type = base::self_type_for_closure(ccx, closure_did, fn_type);
            debug!("declare_rust_fn function_type={:?} self_type={:?}",
                   function_type, self_type);
            (&function_type.sig, Abi::RustCall, Some(self_type))
        }
        _ => ccx.sess().bug("expected closure or fn")
    };


    let sig = ccx.tcx().erase_late_bound_regions(sig);
    let sig = infer::normalize_associated_type(ccx.tcx(), &sig);
    debug!("declare_rust_fn (after region erasure) sig={:?}", sig);

    let (cconv, llfty) = if abi == Abi::Rust || abi == Abi::RustCall {
        (llvm::CCallConv, type_of::type_of_rust_fn(ccx, env, &sig, abi))
    } else {
        let fty = FnType::new(ccx, abi, &sig, &[]);
        (fty.cconv, fty.to_llvm(ccx))
    };

    // it is ok to directly access sig.0.output because we erased all
    // late-bound-regions above
        debug!("declare_rust_fn llfty={:?}", llfty);
    let llfn = declare_raw_fn(ccx, name, cconv, llfty);

    if sig.output == ty::FnDiverging {
        llvm::SetFunctionAttribute(llfn, llvm::Attribute::NoReturn);
    }

    if abi == Abi::Rust || abi == Abi::RustCall {
        attributes::from_fn_type(ccx, fn_type).apply_llfn(llfn);
    } else {
        FnType::new(ccx, abi, &sig, &[]).add_attributes(llfn);
    }

    llfn
}


/// Declare a global with an intention to define it.
///
/// Use this function when you intend to define a global. This function will
/// return None if the name already has a definition associated with it. In that
/// case an error should be reported to the user, because it usually happens due
/// to user’s fault (e.g. misuse of #[no_mangle] or #[export_name] attributes).
pub fn define_global(ccx: &CrateContext, name: &str, ty: Type) -> Option<ValueRef> {
    if get_defined_value(ccx, name).is_some() {
        None
    } else {
        Some(declare_global(ccx, name, ty))
    }
}


/// Declare a Rust function with an intention to define it.
///
/// Use this function when you intend to define a function. This function will
/// return panic if the name already has a definition associated with it. This
/// can happen with #[no_mangle] or #[export_name], for example.
pub fn define_internal_fn<'a, 'tcx>(ccx: &CrateContext<'a, 'tcx>,
                                    name: &str,
                                    fn_type: ty::Ty<'tcx>) -> ValueRef {
    if get_defined_value(ccx, name).is_some() {
        ccx.sess().fatal(&format!("symbol `{}` already defined", name))
    } else {
        let llfn = declare_fn(ccx, name, fn_type);
        llvm::SetLinkage(llfn, llvm::InternalLinkage);
        llfn
    }
}


/// Get defined or externally defined (AvailableExternally linkage) value by
/// name.
pub fn get_defined_value(ccx: &CrateContext, name: &str) -> Option<ValueRef> {
    debug!("get_defined_value(name={:?})", name);
    let namebuf = CString::new(name).unwrap_or_else(|_|{
        ccx.sess().bug(&format!("name {:?} contains an interior null byte", name))
    });
    let val = unsafe { llvm::LLVMGetNamedValue(ccx.llmod(), namebuf.as_ptr()) };
    if val.is_null() {
        debug!("get_defined_value: {:?} value is null", name);
        None
    } else {
        let (declaration, aext_link) = unsafe {
            let linkage = llvm::LLVMGetLinkage(val);
            (llvm::LLVMIsDeclaration(val) != 0,
             linkage == llvm::AvailableExternallyLinkage as c_uint)
        };
        debug!("get_defined_value: found {:?} value (declaration: {}, \
                aext_link: {})", name, declaration, aext_link);
        if !declaration || aext_link {
            Some(val)
        } else {
            None
        }
    }
}
