import Mathlib.Data.Set.Lattice

/-
# Uniones e intersecciones indexadas
El formalismo para hacer estas operaciones en Lean es muy
similar al que usamos en álgebra superior 1. Esto es, dado un
conjunto de índices I se forma la familia { A_i | i ∈ I }. Con
esta familia podemos hacer ⋃_{i∈I} A_i y ⋂_{i∈I} A_i.
-/

open Set

variable (α : Type*)
variable (ι : Type*) (A B : ι → Set α)
variable (S : Set α)
--Definiciones útiles
#check mem_iInter
#check mem_iUnion


example : (⋂ i, A i) ∪ S = ⋂ i, (A i ∪ S) := by
  ext x; constructor
  · rintro (h | hs)
    · rw [mem_iInter] at *
      intro i
      left
      exact h i
    · rw [mem_iInter]
      intro i
      right
      assumption
  · intro h
    rw [mem_iInter] at h
    --lógica clásica
    by_cases hs : x ∈ S
    · right; assumption
    · left
      rw[mem_iInter]
      intro i
      rcases h i with (hai | hs2)
      · assumption
      · contradiction

example : (⋃ i, A i) ∩ S = ⋃ i, (A i ∩ S) := by
  sorry

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  sorry

example : (⋃ i, A i ∪ B i) = (⋃ i, A i) ∪ ⋃ i, B i := by
  sorry

example (h : ∃ (i : ι), A i = ∅) : ⋂ i, A i = ∅ := by
  sorry

example (h : ∀ (i : ι), A i = ∅) : ⋃ i, A i = ∅ := by
  ext x; constructor
  · intro xu
    rw [mem_iUnion] at xu
    rcases xu with ⟨i, xai⟩
    have hi : A i = ∅ := by exact h i
    rw [hi] at xai
    assumption
  · intro h
    contradiction

example (h : ∀ i, A i ⊆ B i) : ⋂ i, A i ⊆ ⋂ i, B i := by
  sorry

example (h : ∀ i, A i ⊆ B i) : ⋃ i, A i ⊆ ⋃ i, B i := by
  intro x xu
  rw [mem_iUnion] at *
  obtain ⟨i, xai⟩ := xu
  use i
  apply h
  assumption

example (h : ∀ i, S ⊆ A i) : S ⊆ ⋂ i, A i := by
  sorry

example (h : ∀ i, A i ⊆ S) : ⋃ i, A i ⊆ S := by
  intro x xu
  rw [mem_iUnion] at xu
  obtain ⟨i, xai⟩ := xu
  apply h i
  assumption
