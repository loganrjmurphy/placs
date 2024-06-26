import Mathlib.Data.List.Basic

theorem aux {α : Type*} {h : α} {t : List α} : h ∈ h::t := (List.mem_cons_self h t)
theorem aux' {α : Type*} {h : α} {t : List α} (x : { x // x ∈ t }) : ↑x ∈ h :: t :=  by apply List.mem_cons_of_mem ; apply x.property

open List

def attachedMap
  {α β : Type*}
  (l : List α)
  (f : {x // x ∈ l} → β)
  (P : β → Bool)  : List β :=
  l.attach |> List.filterMap (fun x ↦ if P (f x) then f x else none)

theorem filterMap_id_map {α β} (f : α → Option β) (l : List α) :
    filterMap id (map f l) = filterMap f l :=
  filterMap_map ..

theorem attach_map_cons_pos
    {α β : Type*}
    (h : α)
    (t : List α)
    (f : {x // x ∈ h::t} → β)
    (P : β → Bool)
    (h': P (f ⟨h, aux⟩)) :
    attachedMap (h::t) f P =
    f ⟨h,aux⟩ :: attachedMap t (λ x => f ⟨x, aux' x⟩) P := by
  simp_rw [attachedMap, attach, attachWith, pmap, filterMap_cons, h']
  simp (config := {singlePass := true}) only [← filterMap_id_map]
  simp_rw [map_pmap]
  congr 2
  exact pmap_congr t fun a _ h₁ => congrFun rfl

theorem attach_map_cons_neg
    {α β : Type*}
    (h : α)
    (t : List α)
    (f : {x // x ∈ h::t} → β)
    (P : β → Bool)
    (h': ¬ P (f ⟨h, aux⟩)) :
    attachedMap (h::t) f P =
    attachedMap t (λ x => f ⟨x, aux' x⟩) P := by
  simp_rw [attachedMap, attach, attachWith, pmap, filterMap_cons, h']
  simp (config := {singlePass := true}) only [← filterMap_id_map]
  simp_rw [map_pmap]
  congr 1
  simp only [id_eq]
  apply pmap_congr
  simp only [mem_cons, implies_true]
