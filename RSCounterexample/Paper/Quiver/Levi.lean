import RSCounterexample.Paper.Quiver.Multiplicity
import RSCounterexample.Paper.Quiver.CompleteWindow
import RSCounterexample.Paper.Quiver.Schur.Projector
import Mathlib.Algebra.MonoidAlgebra.Grading

/-!
# The Levi Weyl projector

For block sizes `d_0, …, d_{s−1}` the Laurent polynomials in the variables of block `p` embed into
`Laurent (∑_p d_p)` (`Levi.embedBlock`). Products of polynomials in separate blocks have
coefficients that factor over the blocks (`Levi.coeff_prod_embedBlock`), so the Levi Weyl projector
`Levi.schurCoeff` of such a product is the product of the one-block Weyl projectors
(`Levi.schurCoeff_prod_embedBlock`). In particular it is the coefficient of
`∏_p s_{λ^{(p)}}(x_{I_p})` in a finite combination of products of rational Schur polynomials
(`Levi.schurCoeff_leviSchur`, `Levi.schurCoeff_sum_leviSchur`).

For a forward quiver, the cut weights (the sums of the exponents over the vertices `≤ p`) are
additive gradings. The Levi Weyl factor has cut weights zero and the graded piece `ℓ` of `R_Q` has
cut weight `∑_{e : p' → q', p' ≤ p < q'} ℓ_e` at the cut after vertex `p`, which gives the
cut-degree equations (5.6) of the paper: only graded pieces satisfying them contribute to the
multiplicity (`ForwardQuiver.cutDegrees_of_schurCoeff_ne_zero`), and those have all `ℓ_e` at most
the degree bound (`ForwardQuiver.CutDegrees.le_degreeBound`). Hence the multiplicity is the sum over
all graded pieces (`ForwardQuiver.multiplicity_eq_finsum`).

## Main results

* `Schubert.RS.Quiver.Levi.coeff_prod_embedBlock`, `Levi.schurCoeff_prod_embedBlock`.
* `Schubert.RS.Quiver.Levi.schurCoeff_leviSchur`: the Levi projector of a product of rational Schur
  polynomials.
* `Schubert.RS.Quiver.ForwardQuiver.cutDegrees_of_schurCoeff_ne_zero`: (5.6).
* `Schubert.RS.Quiver.ForwardQuiver.multiplicity_eq_finsum`: all graded pieces.
-/

namespace Schubert.RS.Quiver

noncomputable section

open MvPolynomial

/-! ## Substituting Laurent monomials for variables -/

section Substitution

variable {K : Type*} [Fintype K] {m : ℕ}

/-- Substituting the Laurent monomials `x^{w_k}` for the variables sends `y^α` to
`x^{∑_k α_k w_k}`. -/
theorem aeval_single_monomial (w : K → Weight m) (α : K →₀ ℕ) (z : ℤ) :
    aeval (fun k => (AddMonoidAlgebra.single (w k) 1 : Laurent m)) (monomial α z) =
      AddMonoidAlgebra.single (∑ k, α k • w k) z := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun k => by simp)]
  simp only [AddMonoidAlgebra.single_pow, one_pow]
  rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one, AddMonoidAlgebra.coe_algebraMap,
    Function.comp_apply, AddMonoidAlgebra.single_mul_single, zero_add, Algebra.algebraMap_self,
    RingHom.id_apply, mul_one]

/-- The coefficients of a polynomial after substituting Laurent monomials for its variables. -/
theorem coeff_aeval_single [DecidableEq K] (w : K → Weight m) (P : MvPolynomial K ℤ)
    (v : Weight m) :
    (aeval (fun k => (AddMonoidAlgebra.single (w k) 1 : Laurent m)) P).coeff v =
      ∑ α ∈ P.support with ∑ k, α k • w k = v, P.coeff α := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [aeval_single_monomial, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- `h_m` of Laurent monomials `x^{w_k}` is homogeneous of degree `m · c` for an additive grading in
which every `w_k` has degree `c`. -/
theorem aeval_hsymm_mem_gradeBy [DecidableEq K] (φ : Weight m →+ ℤ) (w : K → Weight m) (c : ℤ)
    (hw : ∀ k, φ (w k) = c) (r : ℕ) :
    aeval (fun k => (AddMonoidAlgebra.single (w k) 1 : Laurent m)) (hsymm K ℤ r) ∈
      AddMonoidAlgebra.gradeBy ℤ φ (r * c) := by
  rw [AddMonoidAlgebra.mem_gradeBy_iff]
  intro v hv
  have hv' : (aeval (fun k => (AddMonoidAlgebra.single (w k) 1 : Laurent m))
      (hsymm K ℤ r)).coeff v ≠ 0 := Finsupp.mem_support_iff.mp hv
  rw [coeff_aeval_single] at hv'
  obtain ⟨α, hα, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv'
  rw [Finset.mem_filter] at hα
  have hsize : ∑ k, α k = r := by
    by_contra h
    simp only [coeff_hsymm, h, ↓reduceIte] at hne
    exact hne rfl
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  rw [← hα.2, map_sum]
  simp only [map_nsmul]
  simp only [hw, nsmul_eq_mul]
  rw [← Finset.sum_mul, ← Nat.cast_sum, hsize]

end Substitution

namespace Levi

variable {s : ℕ} (d : Fin s → ℕ)

/-! ## Blocks of variables -/

theorem pos_injective (p : Fin s) : Function.Injective (pos d p) := fun _ _ h =>
  eq_of_heq (Sigma.mk.inj_iff.mp (finSigmaFinEquiv.injective h)).2

/-- Weights of `Laurent (∑_p d_p)` are families of weights of the blocks. -/
def blockSplit : ((p : Fin s) → Weight (d p)) ≃+ Weight (total d) where
  toFun U k := U (finSigmaFinEquiv.symm k).1 (finSigmaFinEquiv.symm k).2
  invFun v p i := v (pos d p i)
  left_inv U := by
    funext p i
    change U (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨p, i⟩)).1
      (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨p, i⟩)).2 = U p i
    rw [Equiv.symm_apply_apply]
  right_inv v := by
    funext k
    simp [pos]
  map_add' _ _ := rfl

@[simp] theorem blockSplit_symm_apply (v : Weight (total d)) (p : Fin s) (i : Fin (d p)) :
    (blockSplit d).symm v p i = v (pos d p i) := rfl

@[simp] theorem blockSplit_apply_pos (U : (p : Fin s) → Weight (d p)) (p : Fin s)
    (i : Fin (d p)) : blockSplit d U (pos d p i) = U p i := by
  change U (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨p, i⟩)).1
    (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨p, i⟩)).2 = U p i
  rw [Equiv.symm_apply_apply]

theorem blockSplit_single_single (p : Fin s) (i : Fin (d p)) (z : ℤ) :
    blockSplit d (Pi.single p (Pi.single i z)) = Pi.single (pos d p i) z := by
  apply (blockSplit d).symm.injective
  rw [AddEquiv.symm_apply_apply]
  funext q j
  rw [blockSplit_symm_apply]
  by_cases hq : q = p
  · subst hq
    simp [Pi.single_apply, (pos_injective d q).eq_iff]
  · have hne : pos d q j ≠ pos d p i := fun h =>
      hq (congrArg Sigma.fst (finSigmaFinEquiv.injective h))
    simp [hq, hne]

theorem blockSplit_single_positiveRoot (p : Fin s) (i j : Fin (d p)) :
    blockSplit d (Pi.single p (positiveRoot i j)) = positiveRoot (pos d p i) (pos d p j) := by
  rw [positiveRoot, Pi.single_sub, map_sub, blockSplit_single_single, blockSplit_single_single,
    positiveRoot]

/-- The Laurent polynomials in the variables of block `p`, inside `Laurent (∑_p d_p)`. -/
def embedBlock (p : Fin s) : Laurent (d p) →+* Laurent (total d) :=
  AddMonoidAlgebra.mapDomainRingHom ℤ
    ((blockSplit d).toAddMonoidHom.comp (AddMonoidHom.single (fun q => Weight (d q)) p))

theorem embedBlock_single (p : Fin s) (u : Weight (d p)) (z : ℤ) :
    embedBlock d p (AddMonoidAlgebra.single u z) =
      AddMonoidAlgebra.single (blockSplit d (Pi.single p u)) z :=
  AddMonoidAlgebra.mapDomain_single

/-- **Coefficients of block-separated products** factor over the blocks. -/
theorem coeff_prod_embedBlock (f : (p : Fin s) → Laurent (d p)) (v : Weight (total d)) :
    (∏ p, embedBlock d p (f p)).coeff v = ∏ p, (f p).coeff ((blockSplit d).symm v p) := by
  classical
  have hf : ∀ p, embedBlock d p (f p) = ∑ u ∈ (f p).coeff.support,
      AddMonoidAlgebra.single (blockSplit d (Pi.single p u)) ((f p).coeff u) := by
    intro p
    conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single (f p)]
    rw [Finsupp.sum, map_sum]
    simp only [embedBlock_single]
  simp only [hf]
  rw [Finset.prod_univ_sum]
  simp only [AddMonoidAlgebra.prod_single]
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  have key : ∀ U : (p : Fin s) → Weight (d p),
      (∑ p, blockSplit d (Pi.single p (U p)) = v) ↔ U = (blockSplit d).symm v := by
    intro U
    rw [← map_sum, Finset.univ_sum_single]
    exact ⟨fun h => by rw [← h, AddEquiv.symm_apply_apply],
      fun h => by rw [h, AddEquiv.apply_symm_apply]⟩
  simp only [key]
  rw [Finset.sum_ite_eq']
  split_ifs with hmem
  · rfl
  · rw [Fintype.mem_piFinset] at hmem
    push Not at hmem
    obtain ⟨p, hp⟩ := hmem
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ p) (Finsupp.notMem_support_iff.mp hp)

theorem blockWeight_pos (lam : (p : Fin s) → Fin (d p) → ℤ) (p : Fin s) (i : Fin (d p)) :
    blockWeight d lam (pos d p i) = lam p (Fin.rev i) := by
  change lam (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨p, i⟩)).1
    (Fin.rev (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨p, i⟩)).2) = lam p (Fin.rev i)
  rw [Equiv.symm_apply_apply]

theorem blockSplit_symm_blockWeight (lam : (p : Fin s) → Fin (d p) → ℤ) (p : Fin s) :
    (blockSplit d).symm (blockWeight d lam) p = lam p ∘ Fin.rev := by
  funext i
  exact blockWeight_pos d lam p i

/-- The Levi Weyl factor is the product of the Weyl factors of the blocks. -/
theorem weylFactor_eq_prod_embedBlock :
    weylFactor d = ∏ p, embedBlock d p (Schubert.RS.weylFactor (d p)) := by
  simp only [weylFactor, Schubert.RS.weylFactor, map_prod, map_sub, map_one, embedBlock_single,
    blockSplit_single_positiveRoot]

/-- **The Levi Weyl projector of a block-separated product** is the product of the Weyl projectors
of the blocks. -/
theorem schurCoeff_prod_embedBlock (f : (p : Fin s) → Laurent (d p))
    (lam : (p : Fin s) → Fin (d p) → ℤ) :
    schurCoeff d (∏ p, embedBlock d p (f p)) lam =
      ∏ p, Schur.weylProjector (lam p ∘ Fin.rev) (f p) := by
  rw [schurCoeff, weylFactor_eq_prod_embedBlock, ← Finset.prod_mul_distrib]
  simp only [← map_mul]
  rw [coeff_prod_embedBlock]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [blockSplit_symm_blockWeight]
  rfl

/-! ## Products of rational Schur polynomials -/

/-- `∏_p s_{Λ^{(p)}}(x_{I_p})` for dominant weights `Λ^{(p)}` of the blocks. -/
def leviSchur (Λ : (p : Fin s) → TauCeti.DominantWeight (d p)) : Laurent (total d) :=
  ∏ p, embedBlock d p (Schur.ratSchur (Λ p))

/-- **The Levi projector detects products of rational Schur polynomials**: for a weight `λ` that is
dominant on every block, the Levi projector of `∏_p s_{Λ^{(p)}}(x_{I_p})` at `λ` is `1` if `Λ = λ`
and `0` otherwise. -/
theorem schurCoeff_leviSchur (Λ : (p : Fin s) → TauCeti.DominantWeight (d p))
    (lam : (p : Fin s) → Fin (d p) → ℤ) (hlam : ∀ p, Antitone (lam p)) :
    schurCoeff d (leviSchur d Λ) lam = if (fun p => (Λ p).1) = lam then 1 else 0 := by
  rw [leviSchur, schurCoeff_prod_embedBlock]
  have h : ∀ p, Schur.weylProjector (lam p ∘ Fin.rev) (Schur.ratSchur (Λ p)) =
      if (Λ p).1 = lam p then 1 else 0 := by
    intro p
    rw [Schur.weylProjector_ratSchur (lam p ∘ Fin.rev)
      (fun x y hxy => hlam p (Fin.rev_le_rev.mpr hxy))]
    have hrev : (lam p ∘ Fin.rev) ∘ ⇑(Fin.revPerm : Equiv.Perm (Fin (d p))) = lam p := by
      funext i
      simp
    rw [hrev]
  simp only [h]
  rw [Finset.prod_boole]
  congr 1
  simp only [Finset.mem_univ, true_implies, eq_iff_iff]
  exact ⟨fun h => funext h, fun h p => congrFun h p⟩

theorem schurCoeff_add (f g : Laurent (total d)) (lam : (p : Fin s) → Fin (d p) → ℤ) :
    schurCoeff d (f + g) lam = schurCoeff d f lam + schurCoeff d g lam := by
  simp [schurCoeff, mul_add]

theorem schurCoeff_intCast_mul (z : ℤ) (f : Laurent (total d)) (lam : (p : Fin s) → Fin (d p) → ℤ) :
    schurCoeff d ((z : Laurent (total d)) * f) lam = z * schurCoeff d f lam := by
  rw [schurCoeff, schurCoeff, mul_left_comm, AddMonoidAlgebra.intCast_def]
  simp

theorem schurCoeff_sum {ι : Type*} (S : Finset ι) (f : ι → Laurent (total d))
    (lam : (p : Fin s) → Fin (d p) → ℤ) :
    schurCoeff d (∑ i ∈ S, f i) lam = ∑ i ∈ S, schurCoeff d (f i) lam := by
  rw [schurCoeff, Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum,
    Finset.sum_apply]
  rfl

/-- **Uniqueness of Levi Schur expansions**: in a finite combination of products of rational Schur
polynomials, the coefficient of `∏_p s_{λ^{(p)}}(x_{I_p})` is the Levi projector at `λ`. -/
theorem schurCoeff_sum_leviSchur {ι : Type*} (S : Finset ι)
    (Λ : ι → (p : Fin s) → TauCeti.DominantWeight (d p)) (z : ι → ℤ)
    (lam : (p : Fin s) → Fin (d p) → ℤ) (hlam : ∀ p, Antitone (lam p)) :
    schurCoeff d (∑ i ∈ S, (z i : Laurent (total d)) * leviSchur d (Λ i)) lam =
      ∑ i ∈ S, if (fun p => (Λ i p).1) = lam then z i else 0 := by
  rw [schurCoeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [schurCoeff_intCast_mul, schurCoeff_leviSchur d _ lam hlam]
  split_ifs <;> simp

/-! ## Cut weights -/

/-- The cut weight after block `p`: the sum of the exponents of the variables in blocks `≤ p`. -/
def cutWeight (p : Fin s) : Weight (total d) →+ ℤ where
  toFun w := ∑ k ∈ Finset.univ.filter (fun k => (finSigmaFinEquiv.symm k).1 ≤ p), w k
  map_zero' := by simp
  map_add' v w := by simp [Finset.sum_add_distrib]

theorem cutWeight_single (p q : Fin s) (i : Fin (d q)) :
    cutWeight d p (Pi.single (pos d q i) 1) = if q ≤ p then 1 else 0 := by
  change ∑ k ∈ Finset.univ.filter (fun k => (finSigmaFinEquiv.symm k).1 ≤ p),
    (Pi.single (pos d q i) (1 : ℤ) : Weight (total d)) k = _
  rw [Finset.sum_pi_single']
  simp [pos]

theorem cutWeight_positiveRoot (p q q' : Fin s) (i : Fin (d q)) (j : Fin (d q')) :
    cutWeight d p (positiveRoot (pos d q i) (pos d q' j)) =
      (if q ≤ p then 1 else 0) - (if q' ≤ p then 1 else 0) := by
  rw [positiveRoot, map_sub, cutWeight_single, cutWeight_single]

theorem cutWeight_blockWeight (p : Fin s) (lam : (q : Fin s) → Fin (d q) → ℤ) :
    cutWeight d p (blockWeight d lam) = ∑ q ∈ Finset.univ.filter (· ≤ p), ∑ i, lam q i := by
  change ∑ k ∈ Finset.univ.filter (fun k => (finSigmaFinEquiv.symm k).1 ≤ p),
    blockWeight d lam k = _
  rw [Finset.sum_filter, ← Equiv.sum_comp finSigmaFinEquiv, Fintype.sum_sigma, Finset.sum_filter]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Equiv.symm_apply_apply]
  change ∑ i, (if q ≤ p then blockWeight d lam (pos d q i) else 0) = _
  simp only [blockWeight_pos]
  split_ifs
  · exact Equiv.sum_comp Fin.revPerm (lam q)
  · simp

/-- The Levi Weyl factor has cut weight zero. -/
theorem weylFactor_mem_gradeBy (p : Fin s) :
    weylFactor d ∈ AddMonoidAlgebra.gradeBy ℤ (cutWeight d p) 0 := by
  have h : ∀ q (i j : Fin (d q)), (1 - AddMonoidAlgebra.single
      (positiveRoot (pos d q i) (pos d q j)) 1 : Laurent (total d)) ∈
        AddMonoidAlgebra.gradeBy ℤ (cutWeight d p) 0 := by
    intro q i j
    refine Submodule.sub_mem _ SetLike.GradedOne.one_mem ?_
    have hs := AddMonoidAlgebra.single_mem_gradeBy (cutWeight d p)
      (positiveRoot (pos d q i) (pos d q j)) (1 : ℤ)
    rwa [cutWeight_positiveRoot, sub_self] at hs
  have := SetLike.prod_mem_graded (A := AddMonoidAlgebra.gradeBy ℤ (cutWeight d p))
    (F := Finset.univ) (i := fun _ => (0 : ℤ)) (g := fun q => ∏ i : Fin (d q),
      ∏ j ∈ Finset.univ.filter (i < ·),
        (1 - AddMonoidAlgebra.single (positiveRoot (pos d q i) (pos d q j)) 1 : Laurent (total d)))
    (fun q _ => by
      have := SetLike.prod_mem_graded (A := AddMonoidAlgebra.gradeBy ℤ (cutWeight d p))
        (F := Finset.univ) (i := fun _ => (0 : ℤ)) (g := fun i : Fin (d q) =>
          ∏ j ∈ Finset.univ.filter (i < ·),
            (1 - AddMonoidAlgebra.single (positiveRoot (pos d q i) (pos d q j)) 1 :
              Laurent (total d)))
        (fun i _ => by
          have := SetLike.prod_mem_graded (A := AddMonoidAlgebra.gradeBy ℤ (cutWeight d p))
            (F := Finset.univ.filter (i < ·)) (i := fun _ => (0 : ℤ))
            (g := fun j => (1 - AddMonoidAlgebra.single (positiveRoot (pos d q i) (pos d q j)) 1 :
              Laurent (total d))) (fun j _ => h q i j)
          simpa using this)
      simpa using this)
  simpa [weylFactor] using this

end Levi

/-! ## Cut degrees for a forward quiver -/

namespace ForwardQuiver

variable (Q : ForwardQuiver)

/-- **The cut-degree equations** (5.6): at the cut after every vertex `p`, the number of arrow
factors crossing the cut equals the size of the weight on the vertices `≤ p`. -/
def CutDegrees (lam : Q.Weight) (ℓ : Q.Arrow → ℕ) : Prop :=
  ∀ p : Fin Q.s, ∑ e, (if Q.src e ≤ p ∧ p < Q.tgt e then (ℓ e : ℤ) else 0) =
    ∑ q ∈ Finset.univ.filter (· ≤ p), ∑ i, lam q i

theorem arrowMonomial_eq (e : Q.Arrow) :
    Q.arrowMonomial e = fun ij => AddMonoidAlgebra.single
      (positiveRoot (Q.pos (Q.src e) ij.1) (Q.pos (Q.tgt e) ij.2)) 1 := rfl

/-- The graded piece `ℓ` of `R_Q` has cut weight `∑_{e crossing the cut} ℓ_e`. -/
theorem gradedCharacter_mem_gradeBy (ℓ : Q.Arrow → ℕ) (p : Fin Q.s) :
    Q.gradedCharacter ℓ ∈ AddMonoidAlgebra.gradeBy ℤ (Levi.cutWeight Q.dim p)
      (∑ e, if Q.src e ≤ p ∧ p < Q.tgt e then (ℓ e : ℤ) else 0) := by
  classical
  apply SetLike.prod_mem_graded
  intro e _
  have hc : ∀ ij : Fin (Q.dim (Q.src e)) × Fin (Q.dim (Q.tgt e)),
      Levi.cutWeight Q.dim p (positiveRoot (Q.pos (Q.src e) ij.1) (Q.pos (Q.tgt e) ij.2)) =
        if Q.src e ≤ p ∧ p < Q.tgt e then 1 else 0 := by
    intro ij
    rw [Levi.cutWeight_positiveRoot]
    have hst := Q.src_lt_tgt e
    rcases le_or_gt (Q.src e) p with h1 | h1 <;> rcases le_or_gt (Q.tgt e) p with h2 | h2
    · simp [h1, h2, not_lt.mpr h2]
    · simp [h1, h2]
    · exact absurd (h1.trans (hst.trans_le h2)) (lt_irrefl p)
    · simp [not_le.mpr h1, not_le.mpr h2]
  have hm := aeval_hsymm_mem_gradeBy (Levi.cutWeight Q.dim p)
    (fun ij : Fin (Q.dim (Q.src e)) × Fin (Q.dim (Q.tgt e)) =>
      positiveRoot (Q.pos (Q.src e) ij.1) (Q.pos (Q.tgt e) ij.2)) _ hc (ℓ e)
  rw [arrowMonomial_eq]
  convert hm using 2
  split_ifs <;> simp

/-- **Only graded pieces satisfying the cut-degree equations contribute** ((5.6) of the paper). -/
theorem cutDegrees_of_schurCoeff_ne_zero {lam : Q.Weight} {ℓ : Q.Arrow → ℕ}
    (h : Q.schurCoeff (Q.gradedCharacter ℓ) lam ≠ 0) : Q.CutDegrees lam ℓ := by
  intro p
  have hmem := SetLike.mul_mem_graded (Levi.weylFactor_mem_gradeBy Q.dim p)
    (Q.gradedCharacter_mem_gradeBy ℓ p)
  rw [AddMonoidAlgebra.mem_gradeBy_iff] at hmem
  have hv := hmem (Finsupp.mem_support_iff.mpr h)
  simp only [Set.mem_preimage, Set.mem_singleton_iff, zero_add] at hv
  rw [← hv, Levi.cutWeight_blockWeight]

theorem schurCoeff_gradedCharacter_eq_zero {lam : Q.Weight} {ℓ : Q.Arrow → ℕ}
    (h : ¬ Q.CutDegrees lam ℓ) : Q.schurCoeff (Q.gradedCharacter ℓ) lam = 0 := by
  by_contra h'
  exact h (Q.cutDegrees_of_schurCoeff_ne_zero h')

/-- The cut-degree equations bound every arrow degree by the degree bound. -/
theorem CutDegrees.le_degreeBound {Q : ForwardQuiver} {lam : Q.Weight} {ℓ : Q.Arrow → ℕ}
    (h : Q.CutDegrees lam ℓ)
    (e : Q.Arrow) : ℓ e ≤ Q.degreeBound lam := by
  have h1 := h (Q.src e)
  have hle : (ℓ e : ℤ) ≤
      ∑ e', (if Q.src e' ≤ Q.src e ∧ Q.src e < Q.tgt e' then (ℓ e' : ℤ) else 0) := by
    have := Finset.single_le_sum (f := fun e' => if Q.src e' ≤ Q.src e ∧ Q.src e < Q.tgt e' then
      (ℓ e' : ℤ) else 0) (fun e' _ => by split_ifs <;> positivity) (Finset.mem_univ e)
    simpa [Q.src_lt_tgt e] using this
  have hB : ∑ q ∈ Finset.univ.filter (· ≤ Q.src e), ∑ i, lam q i ≤ (Q.degreeBound lam : ℤ) := by
    rw [degreeBound, Nat.cast_sum]
    calc ∑ q ∈ Finset.univ.filter (· ≤ Q.src e), ∑ i, lam q i
        ≤ ∑ q ∈ Finset.univ.filter (· ≤ Q.src e), ∑ i, ((lam q i).natAbs : ℤ) :=
          Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun i _ => Int.le_natAbs
      _ ≤ ∑ q, ∑ i, ((lam q i).natAbs : ℤ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun q _ _ => Finset.sum_nonneg fun i _ => Int.natCast_nonneg _
      _ = ∑ q, ((∑ i, (lam q i).natAbs : ℕ) : ℤ) := by simp [Nat.cast_sum]
  exact_mod_cast hle.trans (h1.le.trans hB)

/-- The multiplicity is the sum of the Levi projectors over any box of degrees containing the degree
bound. -/
theorem multiplicity_eq_sum_of_le (lam : Q.Weight) {B : ℕ} (hB : Q.degreeBound lam ≤ B) :
    Q.multiplicity lam = ∑ ℓ ∈ Fintype.piFinset (fun _ : Q.Arrow => Finset.range (B + 1)),
      Q.schurCoeff (Q.gradedCharacter ℓ) lam := by
  rw [multiplicity]
  apply Finset.sum_subset
  · intro ℓ hℓ
    rw [Fintype.mem_piFinset] at hℓ ⊢
    intro e
    have := Finset.mem_range.mp (hℓ e)
    exact Finset.mem_range.mpr (by omega)
  · intro ℓ _ hℓ
    apply Q.schurCoeff_gradedCharacter_eq_zero
    intro hcut
    apply hℓ
    rw [Fintype.mem_piFinset]
    exact fun e => Finset.mem_range.mpr (Nat.lt_succ_of_le (hcut.le_degreeBound e))

/-- **The multiplicity is the sum over all graded pieces**: only finitely many contribute. -/
theorem multiplicity_eq_finsum (lam : Q.Weight) :
    Q.multiplicity lam = ∑ᶠ ℓ : Q.Arrow → ℕ, Q.schurCoeff (Q.gradedCharacter ℓ) lam := by
  rw [multiplicity]
  refine (finsum_eq_sum_of_support_subset _ ?_).symm
  intro ℓ hℓ
  rw [Function.mem_support] at hℓ
  have hcut := Q.cutDegrees_of_schurCoeff_ne_zero hℓ
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  exact fun e => Finset.mem_range.mpr (Nat.lt_succ_of_le (hcut.le_degreeBound e))

end ForwardQuiver

end

end Schubert.RS.Quiver
