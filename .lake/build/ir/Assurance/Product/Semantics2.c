// Lean compiler output
// Module: Assurance.Product.Semantics2
// Imports: Init Assurance.Product.GSN2
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
uint8_t l_List_all___rarg(lean_object*, lean_object*);
extern uint8_t l_instDecidableTrue;
LEAN_EXPORT lean_object* l___private_Assurance_Product_Semantics2_0__GSN_deductive_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_GSN_supported(lean_object*);
static lean_object* l_GSN_supported___closed__1;
LEAN_EXPORT lean_object* l_GSN_supported___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Assurance_Product_Semantics2_0__GSN_supported_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_instDecidableFalse;
LEAN_EXPORT lean_object* l___private_Assurance_Product_Semantics2_0__GSN_supported_match__2_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Assurance_Product_Semantics2_0__GSN_deductive_match__2_splitter(lean_object*);
static lean_object* _init_l_GSN_supported___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_GSN_supported___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_GSN_supported(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
lean_dec(x_1);
x_2 = l_instDecidableTrue;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = l_instDecidableFalse;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_GSN_supported___closed__1;
x_7 = l_List_all___rarg(x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_GSN_supported___closed__1;
x_12 = l_List_all___rarg(x_10, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_GSN_supported___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_GSN_supported(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Assurance_Product_Semantics2_0__GSN_supported_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_5, lean_box(0));
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_apply_3(x_4, x_10, x_11, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Assurance_Product_Semantics2_0__GSN_supported_match__2_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Assurance_Product_Semantics2_0__GSN_supported_match__2_splitter___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Assurance_Product_Semantics2_0__GSN_deductive_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_4, lean_box(0));
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Assurance_Product_Semantics2_0__GSN_deductive_match__2_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Assurance_Product_Semantics2_0__GSN_deductive_match__2_splitter___rarg), 3, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Assurance_Product_GSN2(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Assurance_Product_Semantics2(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Assurance_Product_GSN2(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_GSN_supported___closed__1 = _init_l_GSN_supported___closed__1();
lean_mark_persistent(l_GSN_supported___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
