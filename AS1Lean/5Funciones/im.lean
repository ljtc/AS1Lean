import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function

--imágenes directas e inversas

open Function
open Set

#check congrArg
#check funext
#check congrFun
#check mem_image
#check mem_preimage
#check comp
#check comp_apply

--Sean `α` y `β`dos tipos
variable (α β γ : Type*)

--Sea `f` una función de `α` en `β`
variable (f : α → β) (g : β → γ)

--Sean `S`, `T` suconjuntos de `α` y `U`, `V` subconjuntos de `β`
variable (S T : Set α) (U V : Set β)

--### Imagen directa
example : f '' (S ∪ T) = f '' S ∪ f '' T := by
  ext y; constructor
  · intro h
    rw [mem_image] at h
    obtain ⟨x, ⟨xst, fxy⟩⟩ := h
    rw [mem_union] at xst
    rcases xst with (xs | xt)
    · left
      rw [mem_image]
      use x
    · right
      rw [mem_image]
      use x
  · rintro (yfs | yft)
    · rw [mem_image] at *
      obtain ⟨x, ⟨xs, fxy⟩⟩ := yfs
      use x
      constructor
      · left; assumption
      · assumption
    · rw [mem_image] at *
      obtain ⟨x, ⟨xt, fxy⟩⟩ := yft
      use x
      constructor
      · right
        assumption
      · assumption

example : f '' (S ∪ T) = f '' S ∪ f '' T := by
  ext y; constructor
  · intro h
    rcases h with ⟨x,⟨(xs | xt), fxy⟩⟩
    · left
      rw [mem_image]
      use x
    · right
      rw [mem_image]
      use x
  · rintro (⟨x, ⟨xs, fxy⟩⟩ | ⟨x, ⟨xt, fxy⟩⟩)
    · rw [mem_image]
      use x
      constructor
      · left; assumption
      · assumption
    · rw [mem_image]
      use x
      constructor
      · right; assumption
      · assumption


--### Imagen inversa
example : f ⁻¹' (U ∩ V) = f ⁻¹' U ∩ f ⁻¹' V := by
  ext x; constructor
  · intro h
    rw [mem_preimage] at h
    rcases h with ⟨hu, hv⟩
    constructor
    · rw [mem_preimage]
      assumption
    · rw [mem_preimage]
      assumption
  · intro ⟨xu, xv⟩
    rw [mem_preimage] at *
    exact ⟨xu, xv⟩

example : f ⁻¹' (U ∩ V) = f ⁻¹' U ∩ f ⁻¹' V := by
  ext x; constructor
  · intro h
    rw [mem_preimage] at h
    rcases h with ⟨xu, xv⟩
    constructor
    · rw [mem_preimage]
      assumption
    · rw [mem_preimage]
      assumption
  · intro ⟨xu, xv⟩
    rw [mem_preimage] at *
    constructor
    assumption'


--con los dos

example : S ⊆ f ⁻¹' (f '' S) := by
  intro x xs
  rw [mem_preimage, mem_image]
  use x

example : f '' (f ⁻¹' U) ⊆ U := by
  intro y h
  rw [mem_image] at h
  obtain ⟨x, ⟨xp, fxy⟩⟩ := h
  rw [mem_preimage] at xp
  rw [<-fxy]
  assumption
