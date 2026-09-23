import Schubert.RS.LaurentPrefixSupport

/-! The least coefficient of a product with prefix-bounded support. -/

namespace Schubert.RS
noncomputable section
variable {n : ℕ}

theorem prefixSupported_mul_initial {a b : Weight n} {p q : Laurent n}
    (hp : PrefixSupported a p) (hq : PrefixSupported b q) :
    (p*q).coeff (a+b) = p.coeff a * q.coeff b := by
  classical
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
  have h := Finset.sum_eq_single a
    (s := p.coeff.support) (f := fun v => p.coeff v * q.coeff (-v+(a+b)))
  have he : ∀ v ∈ p.coeff.support, v ≠ a → p.coeff v * q.coeff (-v+(a+b)) = 0 := by
    intro v hv hne
    have hpa := hp v (Finsupp.mem_support_iff.mp hv)
    suffices q.coeff (-v+(a+b)) = 0 by simp [this]
    by_contra hn
    have hqb := hq _ hn
    have hva : PrefixLE v a := by
      intro k
      have hh := hqb k
      have heq : -v+(a+b) = (a-v)+b := by abel
      rw [heq, prefixWeight_add, prefixWeight_sub] at hh
      omega
    exact hne (hva.antisymm hpa)
  rw [h he (by intro ha; simp [Finsupp.notMem_support_iff.mp ha])]
  simp

theorem weylFactor_constant (n : ℕ) : (weylFactor n).coeff 0 = 1 := by
  classical
  have prod_initial {ι : Type} (s : Finset ι) (f : ι → Laurent n)
      (hs : ∀ i ∈ s, PrefixSupported 0 (f i)) (hc : ∀ i ∈ s, (f i).coeff 0 = 1) :
      (∏ i ∈ s, f i).coeff 0 = 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      have h := prefixSupported_mul_initial (hs i (Finset.mem_insert_self _ _))
        (PrefixSupported.prod_zero s f (fun j hj => hs j (Finset.mem_insert_of_mem hj)))
      simpa [hc i (Finset.mem_insert_self _ _),
        ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))
          (fun j hj => hc j (Finset.mem_insert_of_mem hj))] using h
  have factor_support (i j : Fin n) (hij : i < j) :
      PrefixSupported 0 (1 - AddMonoidAlgebra.single (positiveRoot i j) 1 : Laurent n) := by
    apply PrefixSupported.one.sub
    intro w hw
    have he : positiveRoot i j = w := by by_contra hn; simp [hn] at hw
    rw [← he, ← rootWeight_rootDegree i j hij]
    simpa using prefixLE_add_rootWeight (0 : Weight n) (rootDegree i j)
  unfold weylFactor
  apply prod_initial
  · intro i hi
    exact PrefixSupported.prod_zero _ _ (fun j hj => factor_support i j (Finset.mem_filter.mp hj).2)
  · intro i hi
    apply prod_initial
    · intro j hj
      exact factor_support i j (Finset.mem_filter.mp hj).2
    · intro j hj
      have hij := (Finset.mem_filter.mp hj).2
      have hn : positiveRoot i j ≠ 0 := by
        intro he
        have h := congrArg (fun w => prefixWeight w ⟨i.val+1, by omega⟩) he
        rw [prefixWeight_positiveRoot i j hij] at h
        have hijv : i.val < j.val := hij
        simp [prefixWeight, show i.val+1 ≤ j.val by omega] at h
      simp [hn]

end
end Schubert.RS
