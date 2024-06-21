// Lean compiler output
// Module: Assurance.Product.Analytic
// Imports: Init Assurance.Product.Template
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
LEAN_EXPORT lean_object* l_AnalyticTemplate_apply(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_AnalyticTemplate_toTemplate___elambda__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_AnalyticTemplate_toTemplate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_AnalyticTemplate_apply___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_AnalyticTemplate_toTemplate___rarg(lean_object*);
lean_object* l_GSN_undevGoals(lean_object*);
LEAN_EXPORT lean_object* l_AnalyticTemplate_toTemplate___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_AnalyticTemplate_apply___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_box(0);
lean_inc(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
x_8 = lean_apply_1(x_1, x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
x_17 = lean_box(0);
lean_inc(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_16);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_16);
x_21 = lean_apply_1(x_1, x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_AnalyticTemplate_apply(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_AnalyticTemplate_apply___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_AnalyticTemplate_toTemplate___elambda__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_AnalyticTemplate_apply___rarg(x_1, x_2);
x_4 = l_GSN_undevGoals(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_AnalyticTemplate_toTemplate___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_AnalyticTemplate_toTemplate___elambda__1___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_AnalyticTemplate_toTemplate___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_AnalyticTemplate_toTemplate___elambda__1___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_AnalyticTemplate_toTemplate(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_AnalyticTemplate_toTemplate___rarg), 1, 0);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Assurance_Product_Template(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Assurance_Product_Analytic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Assurance_Product_Template(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
