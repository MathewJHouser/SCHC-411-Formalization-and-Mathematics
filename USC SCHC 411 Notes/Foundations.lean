/- Universes -/

#check Prop 
#check Nat
#check Float 
#check String 
#check Bool 

#check Type 0
#check Type
#check Type 6

/-Declare Universe Variables-/
universe u₁ u₂ u₃ 

variable (α : Type u₁) (β : Type u₂) (f : α → β)

#check α → β 

#check List Type 

#check Sort 2

variable (γ : Type → Type)

#check ∀ (ty : Type), γ ty 

variable (p : Type → Prop)

#check ∀ (ty : Type), p ty

example {q : Prop} (h₁ h₂ : q) : h₁ = h₂ := rfl 

def root (n : Nat) (h: ∃ m, m*m = n) : Nat :=  
  match h with 
  | Exists.intro m _ => m 

#check Nonempty 
#check Classical.choice 








