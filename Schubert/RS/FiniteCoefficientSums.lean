import Schubert.RS.Laurent
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Generic finite-sum identities, kept abstract in their index types. -/

namespace Schubert.RS
noncomputable section

theorem triple_sum_product {α β γ R : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [CommSemiring R] (f : α → R) (g : β → R) (h : γ → R) :
    (∑ a, f a) * (∑ b, g b) * (∑ c, h c) =
      ∑ t : α × (β × γ), f t.1 * g t.2.1 * h t.2.2 := by
  simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext b
    rw [Finset.sum_comm]
  exact Finset.sum_comm

theorem coefficient_sum_single_subtype {α G R : Type*} [Fintype α]
    [AddMonoid G] [Semiring R] (w : α → G) (z : α → R) (v : G)
    (P : α → Prop) [Fintype {a // P a}] (hP : ∀ a, w a = v ↔ P a) :
    (∑ a, AddMonoidAlgebra.single (w a) (z a)).coeff v = ∑ a : {a // P a}, z a.val := by
  classical
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hP]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (F := inferInstance) _ (by intro a; simp) z

end
end Schubert.RS
