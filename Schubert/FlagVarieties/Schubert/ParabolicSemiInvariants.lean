import Schubert.FlagVarieties.Schubert.SimpleSchubertFlags

/-!
# Semi-invariant functions on `Pᵢ`

`B` acts on the minimal parabolic `Pᵢ` by right multiplication. The comorphism is
`FlagVarieties.parabolicCoaction R n i : 𝒪(Pᵢ) → 𝒪(Pᵢ) ⊗ 𝒪(B)`, the coaction of `𝒪(GLₙ)` reduced
modulo the ideal of `Pᵢ` (`FlagVarieties.parabolicCoaction_mk`).

* `FlagVarieties.mem_quotientSemiInvariants_parabolicIdeal_iff`: the semi-invariants of weight `η`
  on `Pᵢ` (that is, `H⁰(X_{sᵢ}, 𝓛(η))`, by `sectionsEquivSemiInvariants` and `π⁻¹(X_{sᵢ}) = Pᵢ`) are
  the `f ∈ 𝒪(Pᵢ)` with `ρ(f) = f ⊗ η⁻¹` (`FlagVarieties.IsParabolicSemiInvariant`);
* stability under products, powers and inverses of units;
* the entries `p_{rc}` whose row vanishes to the left of `c` (weight `-e_c`), the determinant
  (weight `-1`) and the `2 × 2` minor `Δ` in rows and columns `i, i + 1` (weight `-eᵢ - e_{i+1}`);
* `FlagVarieties.IsParabolicSemiInvariant.eval_mul`: `f(g b) = f(g) η(b)⁻¹` at points `g ∈ Pᵢ(A)`,
  `b ∈ B(A)`. Here `η(b)` is computed by `FlagVarieties.borelPointOfMatrix_borelCharacterUnit`.
-/

noncomputable section

namespace FlagVarieties

open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] (n : ℕ) (i : ℕ)

/-! ### The right action of `B` on `Pᵢ` -/

/-- **The right action of `B` on `Pᵢ`**, `(p, b) ↦ p b`: the comorphism
`𝒪(Pᵢ) → 𝒪(Pᵢ) ⊗ 𝒪(B)`. -/
def parabolicCoaction : ParabolicCoord R n i →ₐ[R] ParabolicCoord R n i ⊗[R] BorelCoord R n :=
  parabolicPointOfMatrix i
    ((parabolicMatrix R n i).map
        (Algebra.TensorProduct.includeLeft : ParabolicCoord R n i →ₐ[R] _) *
      (borelMatrix R n).map
        (Algebra.TensorProduct.includeRight : BorelCoord R n →ₐ[R] _))
    (by
      rw [Matrix.det_mul]
      exact (isUnit_det_map_ringHom _ (isUnit_det_parabolicMatrix R n i)).mul
        (isUnit_det_map_ringHom _ (isUnit_det_borelMatrix R n)))
    (by
      apply Matrix.BlockTriangular.mul
      · intro r c h
        simp [Matrix.map_apply, parabolicMatrix_blockTriangular R n i h]
      · intro r c h
        have hrc : c < r :=
          lt_of_not_ge fun hrc => (h.trans_le (parabolicBlock_monotone i hrc)).false
        simp [Matrix.map_apply, borelMatrix_blockTriangular R n hrc])

theorem parabolicMatrix_map_parabolicCoaction :
    (parabolicMatrix R n i).map (parabolicCoaction R n i) =
      (parabolicMatrix R n i).map
          (Algebra.TensorProduct.includeLeft : ParabolicCoord R n i →ₐ[R]
            ParabolicCoord R n i ⊗[R] BorelCoord R n) *
        (borelMatrix R n).map
          (Algebra.TensorProduct.includeRight : BorelCoord R n →ₐ[R]
            ParabolicCoord R n i ⊗[R] BorelCoord R n) :=
  parabolicMatrix_map_parabolicPointOfMatrix i _ _ _

/-- The coaction of `𝒪(Pᵢ)` is that of `𝒪(GLₙ)` reduced modulo the ideal of `Pᵢ`. -/
theorem parabolicCoaction_comp_mkₐ :
    (parabolicCoaction R n i).comp (Ideal.Quotient.mkₐ R (parabolicIdeal R n i)) =
      rightCoactionMod R n (parabolicIdeal R n i) := by
  refine genericMatrix_algHom_ext (A := ParabolicCoord R n i ⊗[R] BorelCoord R n) ?_
  ext r c
  have h1 := congrFun (congrFun (parabolicMatrix_map_parabolicCoaction R n i) r) c
  have h2 := congrFun (congrFun (map_rightCoaction_genericMatrix R n) r) c
  simp only [Matrix.map_apply, Matrix.mul_apply] at h1 h2
  rw [Matrix.map_apply, Matrix.map_apply, AlgHom.comp_apply]
  change parabolicCoaction R n i (parabolicMatrix R n i r c) = _
  rw [h1, rightCoactionMod, AlgHom.comp_apply, h2, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
  rfl

theorem parabolicCoaction_mk (f : GLCoord R n) :
    parabolicCoaction R n i (Ideal.Quotient.mk (parabolicIdeal R n i) f) =
      rightCoactionMod R n (parabolicIdeal R n i) f :=
  DFunLike.congr_fun (parabolicCoaction_comp_mkₐ R n i) f

/-- `Pᵢ` is stable under right multiplication by `B`. -/
theorem isBorelStable_parabolicIdeal : IsBorelStable R n (parabolicIdeal R n i) := by
  intro f hf
  rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    ← parabolicCoaction_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]

theorem parabolicCoaction_apply (r c : Fin n) :
    parabolicCoaction R n i (parabolicMatrix R n i r c) =
      ∑ k, Algebra.TensorProduct.includeLeft (S := R) (parabolicMatrix R n i r k) *
        Algebra.TensorProduct.includeRight (borelMatrix R n k c) := by
  have h := congrFun (congrFun (parabolicMatrix_map_parabolicCoaction R n i) r) c
  rw [Matrix.map_apply] at h
  rw [h, Matrix.mul_apply]
  rfl

/-! ### Semi-invariants -/

variable {R n i}

/-- `f ∈ 𝒪(Pᵢ)` is **semi-invariant of weight `η`**: `f(p b) = η(b)⁻¹ f(p)`, i.e.
`ρ(f) = f ⊗ η⁻¹`. -/
def IsParabolicSemiInvariant (η : Fin n → ℤ) (f : ParabolicCoord R n i) : Prop :=
  parabolicCoaction R n i f =
    f ⊗ₜ (((borelCharacterUnit R n η)⁻¹ : (BorelCoord R n)ˣ) : BorelCoord R n)

/-- The semi-invariants of weight `η` on `Pᵢ`, in the model `quotientSemiInvariants` of `H⁰`. -/
theorem mem_quotientSemiInvariants_parabolicIdeal_iff (η : Fin n → ℤ) (f : ParabolicCoord R n i) :
    f ∈ quotientSemiInvariants R n (parabolicIdeal R n i) η ↔ IsParabolicSemiInvariant η f := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective f
  rw [mem_quotientSemiInvariants_iff (isBorelStable_parabolicIdeal R n i), IsParabolicSemiInvariant,
    parabolicCoaction_mk]

namespace IsParabolicSemiInvariant

theorem mul {η η' : Fin n → ℤ} {f f' : ParabolicCoord R n i}
    (hf : IsParabolicSemiInvariant η f) (hf' : IsParabolicSemiInvariant η' f') :
    IsParabolicSemiInvariant (η + η') (f * f') := by
  rw [IsParabolicSemiInvariant, map_mul, hf, hf', Algebra.TensorProduct.tmul_mul_tmul,
    borelCharacterUnit_add, mul_inv (borelCharacterUnit R n η), Units.val_mul]

theorem one : IsParabolicSemiInvariant (R := R) (n := n) (i := i) 0 1 := by
  have h : parabolicCoaction R n i 1 = 1 := (parabolicCoaction R n i).map_one
  rw [IsParabolicSemiInvariant, h, borelCharacterUnit_zero, inv_one, Units.val_one]
  rfl

theorem pow {η : Fin n → ℤ} {f : ParabolicCoord R n i} (hf : IsParabolicSemiInvariant η f)
    (k : ℕ) : IsParabolicSemiInvariant (k • η) (f ^ k) := by
  induction k with
  | zero =>
    rw [zero_smul, pow_zero]
    exact one
  | succ k ih =>
    rw [succ_nsmul, pow_succ]
    exact ih.mul hf

theorem prod {ι : Type*} (s : Finset ι) {η : ι → Fin n → ℤ} {f : ι → ParabolicCoord R n i}
    (hf : ∀ j ∈ s, IsParabolicSemiInvariant (η j) (f j)) :
    IsParabolicSemiInvariant (∑ j ∈ s, η j) (∏ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    exact one
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem inv {η : Fin n → ℤ} {u : (ParabolicCoord R n i)ˣ}
    (hu : IsParabolicSemiInvariant η (u : ParabolicCoord R n i)) :
    IsParabolicSemiInvariant (-η) ((u⁻¹ : (ParabolicCoord R n i)ˣ) : ParabolicCoord R n i) := by
  have h1 : parabolicCoaction R n i ((u⁻¹ : (ParabolicCoord R n i)ˣ) : ParabolicCoord R n i) *
      parabolicCoaction R n i (u : ParabolicCoord R n i) = 1 := by
    rw [← map_mul, Units.inv_mul]
    exact (parabolicCoaction R n i).map_one
  have h2 : parabolicCoaction R n i (u : ParabolicCoord R n i) *
      ((u⁻¹ : (ParabolicCoord R n i)ˣ) : ParabolicCoord R n i) ⊗ₜ[R]
        (((borelCharacterUnit R n (-η))⁻¹ : (BorelCoord R n)ˣ) : BorelCoord R n) = 1 := by
    rw [show parabolicCoaction R n i (u : ParabolicCoord R n i) = _ from hu,
      Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv, borelCharacterUnit_neg, inv_inv,
      Units.inv_mul]
    rfl
  exact left_inv_eq_right_inv h1 h2

end IsParabolicSemiInvariant

/-! ### Basic semi-invariants -/

/-- An entry `p_{rc}` whose row vanishes to the left of `c` is semi-invariant of weight `-e_c`. -/
theorem isParabolicSemiInvariant_entry (r c : Fin n)
    (h : ∀ k : Fin n, k < c → parabolicBlock n i k < parabolicBlock n i r) :
    IsParabolicSemiInvariant (-Pi.single c 1) (parabolicMatrix R n i r c) := by
  have := rightCoactionMod_genericMatrix R n (J := parabolicIdeal R n i) r c
    (fun k hk => Ideal.subset_span ⟨⟨(r, k), h k hk⟩, rfl⟩)
  rw [IsParabolicSemiInvariant, inv_borelCharacterUnit_neg_single]
  exact (parabolicCoaction_mk R n i _).trans this

theorem det_borelMatrix : (borelMatrix R n).det = ((borelCharacterUnit R n 1 : (BorelCoord R n)ˣ) :
    BorelCoord R n) := by
  rw [Matrix.det_of_isUpperTriangular (borelMatrix_blockTriangular R n), borelCharacterUnit,
    Units.coe_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Pi.one_apply, zpow_one, borelDiag, IsUnit.unit_spec]

/-- The determinant is semi-invariant of weight `-1`. -/
theorem isParabolicSemiInvariant_det :
    IsParabolicSemiInvariant (R := R) (i := i) (-1) (parabolicMatrix R n i).det := by
  have h1 : parabolicCoaction R n i (parabolicMatrix R n i).det =
      ((parabolicMatrix R n i).map (parabolicCoaction R n i)).det :=
    (det_map_ringHom (B := ParabolicCoord R n i ⊗[R] BorelCoord R n)
      (parabolicCoaction R n i).toRingHom _).symm
  have h2 : ((parabolicMatrix R n i).map
      (Algebra.TensorProduct.includeLeft : ParabolicCoord R n i →ₐ[R]
        ParabolicCoord R n i ⊗[R] BorelCoord R n)).det =
      (Algebra.TensorProduct.includeLeft : ParabolicCoord R n i →ₐ[R]
        ParabolicCoord R n i ⊗[R] BorelCoord R n) (parabolicMatrix R n i).det := by
    rw [← AlgHom.coe_toRingHom]
    exact det_map_ringHom (B := ParabolicCoord R n i ⊗[R] BorelCoord R n) _ _
  have h3 : ((borelMatrix R n).map
      (Algebra.TensorProduct.includeRight : BorelCoord R n →ₐ[R]
        ParabolicCoord R n i ⊗[R] BorelCoord R n)).det =
      (Algebra.TensorProduct.includeRight : BorelCoord R n →ₐ[R]
        ParabolicCoord R n i ⊗[R] BorelCoord R n) (borelMatrix R n).det := by
    rw [← AlgHom.coe_toRingHom]
    exact det_map_ringHom (B := ParabolicCoord R n i ⊗[R] BorelCoord R n) _ _
  rw [IsParabolicSemiInvariant, h1, parabolicMatrix_map_parabolicCoaction, Matrix.det_mul, h2, h3,
    det_borelMatrix, borelCharacterUnit_neg, inv_inv, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    one_mul]

variable (hi : i + 1 < n)

/-- The `2 × 2` minor `Δ = pᵢᵢ p_{i+1,i+1} - p_{i,i+1} p_{i+1,i}` of `Pᵢ`. -/
def parabolicMinor : ParabolicCoord R n i :=
  parabolicMatrix R n i (rowA n i hi) (rowA n i hi) *
      parabolicMatrix R n i (rowB n i hi) (rowB n i hi) -
    parabolicMatrix R n i (rowA n i hi) (rowB n i hi) *
      parabolicMatrix R n i (rowB n i hi) (rowA n i hi)

theorem parabolicCoaction_apply_block (r c : Fin n) (hr : r.val = i ∨ r.val = i + 1)
    (hc : c.val = i ∨ c.val = i + 1) :
    parabolicCoaction R n i (parabolicMatrix R n i r c) =
      Algebra.TensorProduct.includeLeft (S := R) (parabolicMatrix R n i r (rowA n i hi)) *
          Algebra.TensorProduct.includeRight (borelMatrix R n (rowA n i hi) c) +
        Algebra.TensorProduct.includeLeft (S := R) (parabolicMatrix R n i r (rowB n i hi)) *
          Algebra.TensorProduct.includeRight (borelMatrix R n (rowB n i hi) c) := by
  rw [parabolicCoaction_apply]
  refine Fintype.sum_eq_add _ _ (rowA_ne_rowB n i hi) fun k hk => ?_
  have hA : (rowA n i hi).val = i := rfl
  have hB : (rowB n i hi).val = i + 1 := rfl
  have hk1 : k.val ≠ i := fun h => hk.1 (Fin.ext h)
  have hk2 : k.val ≠ i + 1 := fun h => hk.2 (Fin.ext h)
  rcases lt_or_gt_of_ne hk1 with hlt | hgt
  · rw [parabolicMatrix_blockTriangular R n i
      ((parabolicBlock_lt_iff i r k).mpr ⟨by omega, by omega⟩), map_zero, zero_mul]
  · rw [borelMatrix_blockTriangular R n (show c < k by rw [Fin.lt_def]; omega), map_zero,
      mul_zero]

/-- The minor `Δ` is semi-invariant of weight `-eᵢ - e_{i+1}`. -/
theorem isParabolicSemiInvariant_parabolicMinor :
    IsParabolicSemiInvariant (-Pi.single (rowA n i hi) 1 - Pi.single (rowB n i hi) 1)
      (parabolicMinor (R := R) hi) := by
  have hA : (rowA n i hi).val = i := rfl
  have hB : (rowB n i hi).val = i + 1 := rfl
  have hBA : borelMatrix R n (rowB n i hi) (rowA n i hi) = 0 :=
    borelMatrix_blockTriangular R n (rowA_lt_rowB n i hi)
  have hw : (((borelCharacterUnit R n (-Pi.single (rowA n i hi) 1 - Pi.single (rowB n i hi) 1))⁻¹ :
      (BorelCoord R n)ˣ) : BorelCoord R n) =
      borelMatrix R n (rowA n i hi) (rowA n i hi) *
        borelMatrix R n (rowB n i hi) (rowB n i hi) := by
    rw [sub_eq_add_neg, borelCharacterUnit_add, mul_inv (borelCharacterUnit R n _), Units.val_mul,
      inv_borelCharacterUnit_neg_single,
      inv_borelCharacterUnit_neg_single]
  have ht : ∀ (x : ParabolicCoord R n i) (y : BorelCoord R n),
      x ⊗ₜ[R] y = Algebra.TensorProduct.includeLeft (S := R) x *
        Algebra.TensorProduct.includeRight y := fun x y => by
    rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [IsParabolicSemiInvariant, hw, parabolicMinor, map_sub, map_mul, map_mul,
    parabolicCoaction_apply_block hi _ _ (Or.inl hA) (Or.inl hA),
    parabolicCoaction_apply_block hi _ _ (Or.inr hB) (Or.inr hB),
    parabolicCoaction_apply_block hi _ _ (Or.inl hA) (Or.inr hB),
    parabolicCoaction_apply_block hi _ _ (Or.inr hB) (Or.inl hA), hBA, map_zero, ht]
  simp only [map_sub, map_mul]
  ring

/-! ### Values at points -/

/-- **`f(g b) = f(g) η(b)⁻¹`** for `f` semi-invariant of weight `η`, `g ∈ Pᵢ(A)`, `b ∈ B(A)`. -/
theorem IsParabolicSemiInvariant.eval_mul {η : Fin n → ℤ} {f : ParabolicCoord R n i}
    (hf : IsParabolicSemiInvariant η f) {A : Type*} [CommRing A] [Algebra R A]
    (g b : Matrix (Fin n) (Fin n) A) (hg : IsUnit g.det)
    (hgb : g.BlockTriangular (parabolicBlock n i)) (hb : IsUnit b.det)
    (hbu : b.BlockTriangular id) (hgb' : IsUnit (g * b).det)
    (hgb'' : (g * b).BlockTriangular (parabolicBlock n i)) :
    parabolicPointOfMatrix i (g * b) hgb' hgb'' f =
      parabolicPointOfMatrix i g hg hgb f *
        borelPointOfMatrix R b hb hbu (((borelCharacterUnit R n η)⁻¹ : (BorelCoord R n)ˣ) :
          BorelCoord R n) := by
  let L : ParabolicCoord R n i ⊗[R] BorelCoord R n →ₐ[R] A :=
    Algebra.TensorProduct.lift (parabolicPointOfMatrix i g hg hgb)
      (borelPointOfMatrix R b hb hbu) fun _ _ => Commute.all _ _
  have hL : L.comp (parabolicCoaction R n i) = parabolicPointOfMatrix i (g * b) hgb' hgb'' := by
    apply parabolicMatrix_algHom_ext
    rw [parabolicMatrix_map_parabolicPointOfMatrix]
    ext r c
    rw [Matrix.map_apply, AlgHom.comp_apply, parabolicCoaction_apply, map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_one, map_one, mul_one,
      one_mul]
    exact congrArg₂ (· * ·)
      (congrFun (congrFun (parabolicMatrix_map_parabolicPointOfMatrix i g hg hgb) r) k)
      (congrFun (congrFun (borelMatrix_map_borelPointOfMatrix R b hb hbu) k) c)
  have h := DFunLike.congr_fun hL f
  rw [AlgHom.comp_apply, hf] at h
  rw [← h]
  rfl

/-- **The value of a character at a point of `B`**: `η(b) = ∏ₖ bₖₖ^{ηₖ}`. -/
theorem borelPointOfMatrix_borelCharacterUnit {A : Type*} [CommRing A] [Algebra R A]
    (b : Matrix (Fin n) (Fin n) A) (hb : IsUnit b.det) (hbu : b.BlockTriangular id)
    (u : Fin n → Aˣ) (hu : ∀ k, (u k : A) = b k k) (η : Fin n → ℤ) :
    Units.map (borelPointOfMatrix R b hb hbu : BorelCoord R n →* A) (borelCharacterUnit R n η) =
      ∏ k, u k ^ η k := by
  rw [borelCharacterUnit, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  congr 1
  ext
  rw [Units.coe_map, MonoidHom.coe_ofClass, borelDiag, IsUnit.unit_spec, hu]
  exact congrFun (congrFun (borelMatrix_map_borelPointOfMatrix R b hb hbu) k) k

theorem borelPointOfMatrix_inv_borelCharacterUnit {A : Type*} [CommRing A] [Algebra R A]
    (b : Matrix (Fin n) (Fin n) A) (hb : IsUnit b.det) (hbu : b.BlockTriangular id)
    (u : Fin n → Aˣ) (hu : ∀ k, (u k : A) = b k k) (η : Fin n → ℤ) :
    borelPointOfMatrix R b hb hbu (((borelCharacterUnit R n η)⁻¹ : (BorelCoord R n)ˣ) :
      BorelCoord R n) = (((∏ k, u k ^ η k)⁻¹ : Aˣ) : A) := by
  rw [← borelPointOfMatrix_borelCharacterUnit (R := R) b hb hbu u hu η, ← map_inv]
  rfl

end FlagVarieties
