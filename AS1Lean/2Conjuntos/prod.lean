import Mathlib.Data.Set.Prod

/-
# Producto cartesiano de dos conjuntos
Dados dos conjuntos A y B el producto cartesiano de ellos es
A×B={(a,b)|a∈A ∧ b∈B}

En Lean el símbolo × está reservado para producto de tipos.
El símbolo para producto cartesiano es ×ˢ
-/

open Set

variable (α β : Type*)
variable (A A₁ A₂ : Set α) (B B₁ B₂ : Set β)

--cosas útiles
#check mem_prod --cuando alguien pertenece a un producto
#check mem_singleton_iff --equivalencia de pertenecer a un unitario
#check Prod.mk_inj --cuando dos parejas son iguales

example (ha : A₁ ⊆ A₂) (hb : B₁ ⊆ B₂) : A₁ ×ˢ B₁ ⊆ A₂ ×ˢ B₂ := by
  intro (a, b)
  simp only [mem_prod]
  intro ⟨h1, h2⟩
  constructor
  · apply ha
    assumption
  · apply hb
    assumption

example : A ×ˢ (∅ : Set β) = ∅ := by
  ext ⟨a, b⟩
  constructor
  · simp only [mem_prod]
    intro ⟨ha, hb⟩
    contradiction
  · intro h
    contradiction

example : (∅ : Set α) ×ˢ B = ∅ := by
  ext ⟨a,b⟩
  constructor
  · simp only [mem_prod]
    intro ⟨ha, hb⟩
    contradiction
  · intro h
    contradiction

example (a : α) (b : β) : ({a} : Set α) ×ˢ ({b} : Set β) = {(a, b)} := by
  ext ⟨x, y⟩
  simp only [mem_prod, mem_singleton_iff, Prod.mk_inj]

example : (A₁ ×ˢ B₁) ∩ (A₂ ×ˢ B₂) = (A₁ ∩ A₂) ×ˢ (B₁ ∩ B₂) := by
  ext ⟨x,y⟩
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩
    simp only [mem_prod] at *
    rcases h1 with ⟨h1a, h1b⟩
    rcases h2 with ⟨h2a, h2b⟩
    constructor
    · rw [mem_inter_iff]
      constructor; assumption'
    · rw [mem_inter_iff]
      constructor; assumption'
  · intro h
    simp only [mem_prod] at h
    rcases h with ⟨ha, hb⟩
    rw [mem_inter_iff] at *
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    constructor
    · simp only [mem_prod]
      constructor; assumption'
    · simp only [mem_prod]
      constructor; assumption'

--usando propiedades lógicas
example : (A ×ˢ B₁) ∩ (A ×ˢ B₂) = A ×ˢ (B₁ ∩ B₂) := by
  ext ⟨x,y⟩
  simp only [mem_prod, mem_inter_iff, <-and_and_left]

--dos contenciones con elementos y más prosa
example : (A ×ˢ B₁) ∩ (A ×ˢ B₂) = A ×ˢ (B₁ ∩ B₂) := by
  ext ⟨x,y⟩
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩
    simp only [mem_prod] at *
    exact ⟨h1.1, ⟨h1.2, h2.2⟩⟩
  · intro h
    rw [mem_inter_iff]
    simp only [mem_prod] at *
    rw [mem_inter_iff] at h
    exact ⟨⟨h.1, (h.2).1⟩, ⟨h.1, (h.2).2⟩⟩


example : (A₁ ×ˢ B) ∩ (A₂ ×ˢ B) = (A₁ ∩ A₂) ×ˢ B := by
  ext ⟨x,y⟩
  simp only [mem_prod, mem_inter_iff, <-and_and_right]
