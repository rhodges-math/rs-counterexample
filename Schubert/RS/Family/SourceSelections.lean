import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.BooleanAlgebra

/-! Squarefree source selections and exact marked-pair balance. -/

namespace Schubert.RS.Family
noncomputable section
variable {m p q : ℕ}

abbrev PairedChoice (m p : ℕ) := {s : Finset (Fin m) × Finset (Fin m) //
  s.1.card+s.2.card=2*p-1 ∧ s.1.card≤p}

instance (m p : ℕ) : Fintype (PairedChoice m p) := Fintype.ofFinite _

abbrev PairedTerm (m p q : ℕ) := Finset (Fin m) × (PairedChoice m p × PairedChoice m q)

def BalancedTerm (t : PairedTerm m p q) : Prop :=
  t.1 ⊆ t.2.1.val.1 ∧ Disjoint t.2.1.val.2 t.1 ∧
  t.2.2.val.1=(t.2.1.val.1 \ t.1)ᶜ ∧ t.2.2.val.2=(t.2.1.val.2 ∪ t.1)ᶜ

abbrev BalancedPairedTerm (m p q : ℕ) := {t : PairedTerm m p q // BalancedTerm t}

instance (m p q : ℕ) : Fintype (BalancedPairedTerm m p q) := Fintype.ofFinite _

theorem disjoint_union_sdiff {α : Type*} [DecidableEq α] (e f : Finset α)
    (h : Disjoint e f) : (e ∪ f) \ f=e := by
  ext i
  have hi := Finset.disjoint_left.mp h
  simp only [Finset.mem_sdiff,Finset.mem_union]
  constructor
  · rintro ⟨hi',hf⟩
    exact hi'.resolve_right hf
  · intro he
    exact ⟨Or.inl he,hi he⟩


end
end Schubert.RS.Family
