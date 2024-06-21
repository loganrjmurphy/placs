// Lean compiler output
// Module: Assurance.ProductLine.Analytic
// Imports: Init Assurance.Product.Analytic Assurance.ProductLine.vTemplate
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
LEAN_EXPORT lean_object* l_vAnalyticTemplate_lift___elambda__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_vAnalyticTemplate_vAnalyticTemplate__apply___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_vAnalyticTemplate_lift(lean_object*);
LEAN_EXPORT lean_object* l_vAnalyticTemplate_lift___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_vAnalyticTemplate_lift___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_vAnalyticTemplate_vAnalyticTemplate__apply(lean_object*);
LEAN_EXPORT lean_object* l_vAnalyticTemplate_lift___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Assurance_ProductLine_Analytic_0__List_filterMap__cons_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Assurance_ProductLine_Analytic_0__List_filterMap__cons_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_vAnalyticTemplate_vAnalyticTemplate__apply___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Assurance_ProductLine_Analytic_0__List_filterMap__cons_match__1_splitter(lean_object*, lean_object*);
lean_object* l_prod__derive___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_vAnalyticTemplate_vAnalyticTemplate__apply___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_inc(x_10);
x_15 = lean_alloc_closure((void*)(l_prod__derive___rarg), 4, 2);
lean_closure_set(x_15, 0, x_9);
lean_closure_set(x_15, 1, x_10);
lean_inc(x_14);
lean_inc(x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_17);
lean_inc(x_13);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_apply_1(x_19, x_17);
lean_inc(x_13);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_13);
x_23 = lean_box(0);
lean_inc(x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
LEAN_EXPORT lean_object* l_vAnalyticTemplate_vAnalyticTemplate__apply(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_vAnalyticTemplate_vAnalyticTemplate__apply___rarg___boxed), 14, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_vAnalyticTemplate_vAnalyticTemplate__apply___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_vAnalyticTemplate_vAnalyticTemplate__apply___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_vAnalyticTemplate_lift___elambda__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_vAnalyticTemplate_lift___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_vAnalyticTemplate_lift___elambda__1___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_vAnalyticTemplate_lift___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_vAnalyticTemplate_lift___elambda__1___rarg), 2, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_vAnalyticTemplate_lift(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_vAnalyticTemplate_lift___rarg___boxed), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_vAnalyticTemplate_lift___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_vAnalyticTemplate_lift___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Assurance_ProductLine_Analytic_0__List_filterMap__cons_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Assurance_ProductLine_Analytic_0__List_filterMap__cons_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Assurance_ProductLine_Analytic_0__List_filterMap__cons_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Assurance_ProductLine_Analytic_0__List_filterMap__cons_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Assurance_ProductLine_Analytic_0__List_filterMap__cons_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Assurance_Product_Analytic(uint8_t builtin, lean_object*);
lean_object* initialize_Assurance_ProductLine_vTemplate(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Assurance_ProductLine_Analytic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Assurance_Product_Analytic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Assurance_ProductLine_vTemplate(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
