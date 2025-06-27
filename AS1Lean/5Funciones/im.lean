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
  sorry

example : f '' (S ∪ T) = f '' S ∪ f '' T := by
  sorry


--### Imagen inversa
example : f ⁻¹' (U ∩ V) = f ⁻¹' U ∩ f ⁻¹' V := by
  sorry

example : f ⁻¹' (U ∩ V) = f ⁻¹' U ∩ f ⁻¹' V := by
  sorry
