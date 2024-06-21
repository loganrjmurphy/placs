// Lean compiler output
// Module: Assurance.Example.gsn_example
// Imports: Init Assurance.Product.GSN
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_TargetProperty;
LEAN_EXPORT lean_object* l_AllBehaviours;
LEAN_EXPORT lean_object* l_V___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_V(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_V(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_V___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_V(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_AllBehaviours() {
_start:
{
return lean_box(0);
}
}
static lean_object* _init_l_TargetProperty() {
_start:
{
return lean_box(0);
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Assurance_Product_GSN(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Assurance_Example_gsn__example(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Assurance_Product_GSN(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_AllBehaviours = _init_l_AllBehaviours();
l_TargetProperty = _init_l_TargetProperty();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
