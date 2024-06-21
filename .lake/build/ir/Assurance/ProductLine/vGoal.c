// Lean compiler output
// Module: Assurance.ProductLine.vGoal
// Imports: Init Var Assurance.Product.GSN
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
LEAN_EXPORT lean_object* l_vGoal_instVarGoal___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_vGoal_asGoal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_vGoal_asGoal___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_vGoal_pc___rarg___boxed(lean_object*);
static lean_object* l_vGoal_instVarGoal___closed__1;
LEAN_EXPORT lean_object* l_vGoal_pc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_vGoal_pc___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_vGoal_instVarGoal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_vGoal_pc___rarg(lean_object*);
LEAN_EXPORT lean_object* l_vGoal_asGoal___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_vGoal_pc___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_vGoal_pc(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_vGoal_pc___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_vGoal_pc___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_vGoal_pc___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_vGoal_pc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_vGoal_pc(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_vGoal_asGoal___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_4, x_5, x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_vGoal_asGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_vGoal_asGoal___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_vGoal_asGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_vGoal_asGoal(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_vGoal_instVarGoal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_vGoal_asGoal___rarg), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_vGoal_instVarGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_vGoal_instVarGoal___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_vGoal_instVarGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_vGoal_instVarGoal(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Var(uint8_t builtin, lean_object*);
lean_object* initialize_Assurance_Product_GSN(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Assurance_ProductLine_vGoal(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Var(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Assurance_Product_GSN(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_vGoal_instVarGoal___closed__1 = _init_l_vGoal_instVarGoal___closed__1();
lean_mark_persistent(l_vGoal_instVarGoal___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
