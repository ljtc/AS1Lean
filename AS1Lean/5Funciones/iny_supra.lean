import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function

--funciones inyectivas, suprayectivas y biyectivas

open Function
open Set

#print Injective
#print Surjective
#print Bijective

--Sean `α` y `β`dos tipos
variable (α β γ : Type*)

--Sea `f` una función de `α` en `β`
variable (f : α → β) (g : β → γ)

--### Funciones inyectivas
example (injf : Injective f) (injg : Injective g) :
    Injective (g ∘ f) := by
  sorry

example (injgf : Injective (g ∘ f)) : Injective f := by
  sorry

--### Funciones suprayectivas
example (surf : Surjective f) (surg : Surjective g) :
    Surjective (g ∘ f) := by
  sorry

example (srgf: Surjective (g ∘ f)) : Surjective g := by
  sorry
