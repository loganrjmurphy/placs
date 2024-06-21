// Lean compiler output
// Module: Assurance.Product.Properties
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
uint8_t l_List_all___rarg(lean_object*, lean_object*);
extern uint8_t l_instDecidableTrue;
LEAN_EXPORT lean_object* l___private_Assurance_Product_Properties_0__GSN_supported_match__2_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Assurance_Product_Properties_0__GSN_deductive_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_GSN_supported(lean_object*);
static lean_object* l_GSN_supported___closed__1;
LEAN_EXPORT lean_object* l_GSN_supported___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Assurance_Product_Properties_0__GSN_supported_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Assurance_Product_Properties_0__GSN_supported_match__2_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_instDecidableFalse;
LEAN_EXPORT lean_object* l___private_Assurance_Product_Properties_0__GSN_deductive_match__2_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Assurance_Product_Properties_0__GSN_deductive_match__2_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = l_instDecidableFalse;
return x_2;
}
case 1:
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = l_instDecidableTrue;
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = l_instDecidableFalse;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_GSN_supported___closed__1;
x_8 = l_List_all___rarg(x_4, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_GSN_supported___closed__1;
x_13 = l_List_all___rarg(x_11, x_12);
return x_13;
}
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
LEAN_EXPORT lean_object* l___private_Assurance_Product_Properties_0__GSN_supported_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
case 1:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_3, x_6, lean_box(0));
return x_7;
}
default: 
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_apply_3(x_5, x_11, x_12, x_13);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Assurance_Product_Properties_0__GSN_supported_match__2_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Assurance_Product_Properties_0__GSN_supported_match__2_splitter___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Assurance_Product_Properties_0__GSN_supported_match__2_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Assurance_Product_Properties_0__GSN_supported_match__2_splitter___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Assurance_Product_Properties_0__GSN_deductive_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_3, x_5, lean_box(0));
return x_6;
}
default: 
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_4, x_7, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Assurance_Product_Properties_0__GSN_deductive_match__2_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Assurance_Product_Properties_0__GSN_deductive_match__2_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Assurance_Product_Properties_0__GSN_deductive_match__2_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Assurance_Product_Properties_0__GSN_deductive_match__2_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Assurance_Product_GSN(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Assurance_Product_Properties(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Assurance_Product_GSN(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_GSN_supported___closed__1 = _init_l_GSN_supported___closed__1();
lean_mark_persistent(l_GSN_supported___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
