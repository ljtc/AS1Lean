import Mathlib.Data.Set.Prod

variable {α β γ : Type}

-- Algunos tipos de relación
def reflexive (R : Set (α × α)) : Prop :=
  ∀ a, (a, a) ∈ R

def symmetric (R : Set (α × α)) : Prop :=
  ∀ a b, (a, b) ∈ R → (b, a) ∈ R

def transitive (R : Set (α × α)) : Prop :=
  ∀ a b c, (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R

def irreflexive (R: Set (α × α )) : Prop :=
  ∀ a, (a, a) ∉ R

def antisymmetric (R: Set (α × α )) : Prop :=
  ∀ a b, (a, b) ∈ R → (b, a) ∈ R → a = b

def asymmetric (R: Set (α × α )) : Prop :=
  ∀ a b, (a, b) ∈ R → (b, a) ∉ R


-- Ejemplos de relación
def diag : Set (α × α) := {(a, a) | a : α}

def total : Set (α × α) := ⊤

def empty : Set (α × α) := ⊥

-- Todos están relacionados en la relación total
example (a b : α) : (a, b) ∈ total := by
  trivial

-- Nadie está relacionado en la relación vacía
example (a b : α) : (a, b) ∉ empty := by
  intro h
  contradiction

-- Una pareja está en la diagonal si y sólo si sus entradas son iguales
#check Prod.mk_inj
lemma en_diag {a b : α} : (a, b) ∈ diag ↔ a = b := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h
    have eqs : c = a ∧ c = b := by
      apply (Prod.mk_inj).mp hc
    rcases eqs with ⟨ca, cb⟩
    rw [<- ca, <- cb]
  · intro ab
    use a
    rw [ab]

section

variable (R S : Set (α × α))

--Si R es reflexiva entonces contiene a la diagonal
example (h : reflexive R) : diag ⊆ R := by
  intro (a,b) dab
  obtain ⟨c, hc⟩ := dab
  rw [<- hc]
  apply h

--Si R contiene a la diagonal entonces es reflexiva
example (h : diag ⊆ R) : reflexive R := by
  intro a
  apply h
  use a

example (h1 : irreflexive R) (h2 : transitive R) : asymmetric R := by
  intro a b rab rba
  have raa : (a, a) ∈ R := by
    apply h2
    apply rab
    exact rba
  apply h1 a
  assumption

  end
