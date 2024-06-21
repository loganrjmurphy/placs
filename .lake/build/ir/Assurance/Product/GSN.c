// Lean compiler output
// Module: Assurance.Product.GSN
// Imports: Init Assurance.Product.Goal
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT uint8_t l_GSN_instDecidableEqNil(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GSN_roots(lean_object*);
LEAN_EXPORT lean_object* l_GSN_root_x3f(lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GSN_root(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GSN_undevGoals(lean_object*);
static lean_object* l_GSN_roots___closed__1;
LEAN_EXPORT lean_object* l_GSN_instDecidableEqNil___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_GSN_undevGoals___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at_GSN_roots___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_GSN_roots___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GSN_root___boxed(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT uint8_t l_GSN_instDecidableEqNil(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_GSN_instDecidableEqNil___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_GSN_instDecidableEqNil(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_GSN_root_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
case 1:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
default: 
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_GSN_root(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_GSN_root___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_GSN_root(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_GSN_roots___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_GSN_root_x3f(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_GSN_root_x3f(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at_GSN_roots___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(lean_box(0), x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_1 = x_5;
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_array_push(x_2, x_8);
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
static lean_object* _init_l_GSN_roots___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_GSN_roots(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = l_List_mapTR_loop___at_GSN_roots___spec__1(x_1, x_2);
x_4 = l_GSN_roots___closed__1;
x_5 = l_List_filterMapTR_go___at_GSN_roots___spec__2(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_GSN_undevGoals___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_GSN_undevGoals(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_List_mapTR_loop___at_GSN_undevGoals___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Assurance_Product_Goal(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Assurance_Product_GSN(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Assurance_Product_Goal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_GSN_roots___closed__1 = _init_l_GSN_roots___closed__1();
lean_mark_persistent(l_GSN_roots___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
