use neon::prelude::*;
use mozjs::jsapi::JS_NewGlobalObject;
use mozjs::jsapi::OnNewGlobalHookOption;
use mozjs::jsval::UndefinedValue;
use mozjs::rust::{JSEngine, RealmOptions, Runtime, SIMPLE_GLOBAL_CLASS};

use std::ptr;

fn hello(mut c: FunctionContext) -> JsResult<JsString> {
    let engine = JSEngine::init().unwrap();
    let rt = Runtime::new(engine.handle());
    let cx = rt.cx();

    unsafe {
        let options = RealmOptions::default();
        rooted!(in(cx) let global =
            JS_NewGlobalObject(cx, &SIMPLE_GLOBAL_CLASS, ptr::null_mut(),
                               OnNewGlobalHookOption::FireOnNewGlobalHook,
                               &*options)
        );
        rooted!(in(cx) let mut rval = UndefinedValue());
        assert!(rt.evaluate_script(global.handle(), "1 + 1",
                                   "test", 1, rval.handle_mut()).is_ok());
    }
    Ok(c.string("hello node"))
}

register_module!(mut cx, {
    cx.export_function("hello", hello)
});
