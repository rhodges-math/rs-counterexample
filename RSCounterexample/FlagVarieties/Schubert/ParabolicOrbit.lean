import RSCounterexample.FlagVarieties.Schubert.Parabolic
import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# The closure of `B sᵢ B` is `Pᵢ`

Over every commutative ring `R`, the orbit ideal of a simple reflection is the ideal of the minimal
parabolic subgroup (`FlagVarieties.schubertOrbitIdeal_simpleReflection`):

    closure (B sᵢ B) = Pᵢ.

On the open cell `x_{i+1,i} ≠ 0` of `Pᵢ` the generic point factors as `g = b sᵢ u` with
`b ∈ B` and `u = 1 + (x_{i+1,i+1} / x_{i+1,i}) E_{i,i+1}` (`FlagVarieties.parabolic_factorization`),
and `x_{i+1,i}` is a nonzerodivisor of `𝒪(Pᵢ)`: `𝒪(Pᵢ)` embeds into a localization of a
polynomial ring (`FlagVarieties.toParabolicPolyRing_injective`).
-/

noncomputable section

namespace FlagVarieties

open MvPolynomial

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### Permutation matrices -/

variable {n} in
theorem mul_permMatrix_apply {A : Type*} [CommRing A] (M : Matrix (Fin n) (Fin n) A)
    (w : Equiv.Perm (Fin n)) (r c : Fin n) : (M * permMatrix (A := A) n w) r c = M r (w c) := by
  simp only [Matrix.mul_apply, permMatrix_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (w c) (fun x => M r x)]
  simp

theorem permMatrix_simpleReflection_mul_self {A : Type*} [CommRing A] (i : ℕ) (hi : i + 1 < n) :
    permMatrix (A := A) n (simpleReflection n i hi) * permMatrix n (simpleReflection n i hi) =
      1 := by
  ext r c
  rw [mul_permMatrix_apply, permMatrix_apply, simpleReflection, Equiv.swap_apply_self,
    Matrix.one_apply]

/-- The matrix of a point `(b, b')` of `B × B` under the orbit comorphism: `b ẇ b'`. -/
theorem pointMatrix_pairLift_comp {A : Type u} [CommRing A] [Algebra R A]
    (w : Equiv.Perm (Fin n)) (β β' : BorelCoord R n →ₐ[R] A) :
    GLScheme.pointMatrix R n ((pairLift β β').comp (schubertOrbitComorphism R n w)) =
      (borelMatrix R n).map β * permMatrix n w * (borelMatrix R n).map β' := by
  let ℓ := pairLift β β'
  have hmap : ∀ M N : Matrix (Fin n) (Fin n) (BorelPairRing R n),
      (M * N).map ℓ = M.map ℓ * N.map ℓ := fun M N => Matrix.map_mul (f := ℓ.toRingHom)
  have hl : ((borelMatrix R n).map (pairInl R n)).map ℓ = (borelMatrix R n).map β := by
    rw [Matrix.map_map, ← AlgHom.coe_comp, pairLift_comp_pairInl]
  have hr : ((borelMatrix R n).map (pairInr R n)).map ℓ = (borelMatrix R n).map β' := by
    rw [Matrix.map_map, ← AlgHom.coe_comp, pairLift_comp_pairInr]
  have hp : (permMatrix (A := BorelPairRing R n) n w).map ℓ = permMatrix n w :=
    permMatrix_map (v := w) ℓ
  rw [pointMatrix_comp, schubertOrbitComorphism, pointMatrix_glPointOfMatrix, schubertOrbitMatrix,
    hmap, hmap, hl, hr, hp]

/-! ### `𝒪(Pᵢ)` embeds into a localized polynomial ring -/

variable (i : ℕ)

/-- The generic point of `Pᵢ` over `R[xᵢⱼ]`: `x_{rc}` on and above the block diagonal, `0` below. -/
def parabolicPolyMatrix : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) R) :=
  Matrix.of fun r c => if parabolicBlock n i c < parabolicBlock n i r then 0 else X (r, c)

/-- `R[xᵢⱼ][det⁻¹]` for the generic point of `Pᵢ`. -/
abbrev ParabolicPolyRing : Type u :=
  Localization.Away (parabolicPolyMatrix R n i).det

/-- The generic point of `Pᵢ` over `ParabolicPolyRing`. -/
def parabolicPolyPoint : Matrix (Fin n) (Fin n) (ParabolicPolyRing R n i) :=
  (parabolicPolyMatrix R n i).map (algebraMap _ _)

theorem isUnit_det_parabolicPolyPoint : IsUnit (parabolicPolyPoint R n i).det := by
  rw [parabolicPolyPoint, det_map_ringHom]
  exact IsLocalization.Away.algebraMap_isUnit _

theorem parabolicPolyPoint_blockTriangular :
    (parabolicPolyPoint R n i).BlockTriangular (parabolicBlock n i) := by
  intro r c h
  simp [parabolicPolyPoint, parabolicPolyMatrix, h]

/-- The embedding `𝒪(Pᵢ) → R[xᵢⱼ][det⁻¹]`. -/
def toParabolicPolyRing : ParabolicCoord R n i →ₐ[R] ParabolicPolyRing R n i :=
  parabolicPointOfMatrix i (parabolicPolyPoint R n i) (isUnit_det_parabolicPolyPoint R n i)
    (parabolicPolyPoint_blockTriangular R n i)

theorem parabolicPolyMatrix_map_aeval :
    (parabolicPolyMatrix R n i).map
        (aeval fun rc : Fin n × Fin n => parabolicMatrix R n i rc.1 rc.2) =
      parabolicMatrix R n i := by
  ext r c
  simp only [parabolicPolyMatrix, Matrix.map_apply, Matrix.of_apply]
  split_ifs with h
  · rw [map_zero]
    exact (parabolicMatrix_blockTriangular R n i h).symm
  · rw [aeval_X]

theorem isUnit_aeval_det_parabolicPolyMatrix :
    IsUnit (aeval (fun rc : Fin n × Fin n => parabolicMatrix R n i rc.1 rc.2)
      (parabolicPolyMatrix R n i).det) := by
  rw [← AlgHom.coe_toRingHom, ← det_map_ringHom]
  change IsUnit ((parabolicPolyMatrix R n i).map
    (aeval fun rc : Fin n × Fin n => parabolicMatrix R n i rc.1 rc.2)).det
  rw [parabolicPolyMatrix_map_aeval]
  exact isUnit_det_parabolicMatrix R n i

/-- The retraction `R[xᵢⱼ][det⁻¹] → 𝒪(Pᵢ)`. -/
def fromParabolicPolyRing : ParabolicPolyRing R n i →ₐ[R] ParabolicCoord R n i :=
  IsLocalization.Away.liftAlgHom (parabolicPolyMatrix R n i).det
    (f := aeval fun rc : Fin n × Fin n => parabolicMatrix R n i rc.1 rc.2)
    (isUnit_aeval_det_parabolicPolyMatrix R n i)

theorem fromParabolicPolyRing_comp_toParabolicPolyRing :
    (fromParabolicPolyRing R n i).comp (toParabolicPolyRing R n i) = AlgHom.id R _ := by
  apply parabolicMatrix_algHom_ext
  ext r c
  rw [Matrix.map_apply, Matrix.map_apply, AlgHom.comp_apply, AlgHom.id_apply]
  have h := congrFun (congrFun (parabolicMatrix_map_parabolicPointOfMatrix (R := R) i
    (parabolicPolyPoint R n i) (isUnit_det_parabolicPolyPoint R n i)
    (parabolicPolyPoint_blockTriangular R n i)) r) c
  rw [Matrix.map_apply] at h
  change fromParabolicPolyRing R n i
    (parabolicPointOfMatrix i _ _ _ (parabolicMatrix R n i r c)) = _
  rw [h, parabolicPolyPoint, Matrix.map_apply, fromParabolicPolyRing,
    IsLocalization.Away.liftAlgHom_apply]
  refine (IsLocalization.lift_eq _ _).trans ?_
  have h2 := congrFun (congrFun (parabolicPolyMatrix_map_aeval R n i) r) c
  rw [Matrix.map_apply] at h2
  exact h2

theorem toParabolicPolyRing_injective : Function.Injective (toParabolicPolyRing R n i) :=
  Function.LeftInverse.injective (g := fromParabolicPolyRing R n i) fun x => by
    change ((fromParabolicPolyRing R n i).comp (toParabolicPolyRing R n i)) x = x
    rw [fromParabolicPolyRing_comp_toParabolicPolyRing, AlgHom.id_apply]

/-- **`x_{i+1,i}` is a nonzerodivisor of `𝒪(Pᵢ)`.** -/
theorem parabolicMatrix_mem_nonZeroDivisors (hi : i + 1 < n) :
    parabolicMatrix R n i ⟨i + 1, hi⟩ ⟨i, by omega⟩ ∈
      nonZeroDivisors (ParabolicCoord R n i) := by
  have hblock : ¬ parabolicBlock n i ⟨i, by omega⟩ < parabolicBlock n i ⟨i + 1, hi⟩ := by
    rw [parabolicBlock_lt_iff]
    simp
  have hto : toParabolicPolyRing R n i (parabolicMatrix R n i ⟨i + 1, hi⟩ ⟨i, by omega⟩) =
      algebraMap (MvPolynomial (Fin n × Fin n) R) (ParabolicPolyRing R n i)
        (X ((⟨i + 1, hi⟩, ⟨i, by omega⟩) : Fin n × Fin n)) := by
    have h := congrFun (congrFun (parabolicMatrix_map_parabolicPointOfMatrix (R := R) i
      (parabolicPolyPoint R n i) (isUnit_det_parabolicPolyPoint R n i)
      (parabolicPolyPoint_blockTriangular R n i)) ⟨i + 1, hi⟩) ⟨i, by omega⟩
    rw [Matrix.map_apply] at h
    rw [toParabolicPolyRing, h, parabolicPolyPoint, Matrix.map_apply]
    simp only [parabolicPolyMatrix, Matrix.of_apply, hblock, ↓reduceIte]
  have hreg : (X ((⟨i + 1, hi⟩, ⟨i, by omega⟩) : Fin n × Fin n) :
      MvPolynomial (Fin n × Fin n) R) ∈ nonZeroDivisors (MvPolynomial (Fin n × Fin n) R) :=
    IsRegular.mem_nonZeroDivisors isRegular_X
  have hX : algebraMap (MvPolynomial (Fin n × Fin n) R) (ParabolicPolyRing R n i)
      (X ((⟨i + 1, hi⟩, ⟨i, by omega⟩) : Fin n × Fin n)) ∈
      nonZeroDivisors (ParabolicPolyRing R n i) :=
    IsLocalization.nonZeroDivisors_le_comap (M := Submonoid.powers (parabolicPolyMatrix R n i).det)
      (S := ParabolicPolyRing R n i) hreg
  rw [mem_nonZeroDivisors_iff] at hX ⊢
  constructor
  · intro a ha
    apply toParabolicPolyRing_injective R n i
    rw [map_zero]
    apply hX.1
    rw [← hto, ← map_mul, ha, map_zero]
  · intro a ha
    apply toParabolicPolyRing_injective R n i
    rw [map_zero]
    apply hX.2
    rw [← hto, ← map_mul, ha, map_zero]

/-! ### The Bruhat factorization on the open cell of `Pᵢ` -/

variable {R n}

theorem transvection_blockTriangular {A : Type*} [CommRing A] {a b : Fin n} (hab : a < b)
    (x : A) : (Matrix.transvection a b x).BlockTriangular id := by
  intro r c h
  have hrc : r ≠ c := (ne_of_lt h).symm
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hrc, zero_add,
    Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'
    exact absurd (h.trans hab) (lt_irrefl _)
  · rfl

/-- **The Bruhat factorization on the open cell of `Pᵢ`**: if `g ∈ Pᵢ(A)` and
`x g_{i+1,i} = g_{i+1,i+1}`, then `g = b sᵢ u` with `b = g (1 - x E_{i,i+1}) sᵢ` upper triangular
and
`u = 1 + x E_{i,i+1}`. -/
theorem parabolic_factorization {A : Type*} [CommRing A] (i : ℕ) (hi : i + 1 < n)
    (g : Matrix (Fin n) (Fin n) A) (hg : g.BlockTriangular (parabolicBlock n i)) (x : A)
    (hx : x * g ⟨i + 1, hi⟩ ⟨i, by omega⟩ = g ⟨i + 1, hi⟩ ⟨i + 1, hi⟩) :
    (g * Matrix.transvection (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩ (-x) *
      permMatrix n (simpleReflection n i hi)).BlockTriangular id ∧
      g = g * Matrix.transvection (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩ (-x) *
        permMatrix n (simpleReflection n i hi) * permMatrix n (simpleReflection n i hi) *
        Matrix.transvection (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩ x := by
  set a : Fin n := ⟨i, by omega⟩
  set a' : Fin n := ⟨i + 1, hi⟩
  have haa' : a ≠ a' := by simp [a, a', Fin.ext_iff]
  constructor
  · intro r c hrc
    change (g * Matrix.transvection a a' (-x) *
      permMatrix (A := A) n (simpleReflection n i hi)) r c = 0
    rw [mul_permMatrix_apply]
    have hT : ∀ q, (g * Matrix.transvection a a' (-x)) r q =
        g r q + (if q = a' then g r a * -x else 0) := by
      intro q
      rw [Matrix.transvection, mul_add, mul_one, Matrix.add_apply]
      split_ifs with hq
      · rw [hq, Matrix.mul_single_apply_same]
      · rw [Matrix.mul_single_apply_of_ne (-x) a a' r q hq, add_zero]
    rw [hT]
    have hgz : ∀ r' c' : Fin n, c'.val < r'.val → ¬(r'.val = i + 1 ∧ c'.val = i) → g r' c' = 0 :=
      fun r' c' h1 h2 => hg ((parabolicBlock_lt_iff i r' c').mpr ⟨h1, h2⟩)
    have hrc' : c.val < r.val := hrc
    have ha : a.val = i := rfl
    have ha' : a'.val = i + 1 := rfl
    by_cases hca : c = a
    · rw [hca, simpleReflection, Equiv.swap_apply_left, ite_eq_left_of_eq_true _ _ (eq_self a')]
      have hra : i < r.val := by rw [hca] at hrc'; omega
      by_cases hr : r = a'
      · rw [hr]
        change g a' a' + g a' a * -x = 0
        rw [← hx]
        ring
      · have hr' : r.val ≠ i + 1 := fun h => hr (Fin.ext h)
        have h1 : g r a' = 0 := hgz r a' (by omega) (by omega)
        have h2 : g r a = 0 := hgz r a (by omega) (by omega)
        rw [h1, h2, zero_mul, add_zero]
    · have hca1 : c.val ≠ i := fun h => hca (Fin.ext h)
      by_cases hca' : c = a'
      · rw [hca', simpleReflection, Equiv.swap_apply_right,
          ite_eq_right_of_eq_false _ _ (eq_false haa'),
          add_zero]
        have hra : i + 1 < r.val := by rw [hca'] at hrc'; omega
        exact hgz r a (by omega) (by omega)
      · have hca2 : c.val ≠ i + 1 := fun h => hca' (Fin.ext h)
        rw [simpleReflection, Equiv.swap_apply_of_ne_of_ne hca hca',
          ite_eq_right_of_eq_false _ _ (eq_false hca'), add_zero]
        exact hgz r c hrc' (by omega)
  · rw [Matrix.mul_assoc (g * _), permMatrix_simpleReflection_mul_self, Matrix.mul_one,
      Matrix.mul_assoc, Matrix.transvection_mul_transvection_same a a' haa', neg_add_cancel,
      Matrix.transvection_zero, Matrix.mul_one]

/-! ### The closure of `B sᵢ B` -/

variable (R n) in
/-- **The closure of `B sᵢ B` is `Pᵢ`** (over every commutative ring): the orbit ideal of the
simple reflection `sᵢ` is the ideal of the minimal parabolic subgroup. -/
theorem schubertOrbitIdeal_simpleReflection (i : ℕ) (hi : i + 1 < n) :
    schubertOrbitIdeal R n (simpleReflection n i hi) = parabolicIdeal R n i := by
  refine le_antisymm ?_ (parabolicIdeal_le_schubertOrbitIdeal R n i hi)
  intro f hf
  set a : Fin n := ⟨i, by omega⟩
  set a' : Fin n := ⟨i + 1, hi⟩
  have haa' : a ≠ a' := by simp [a, a', Fin.ext_iff]
  let y := parabolicMatrix R n i a' a
  let A' := Localization.Away y
  let g : Matrix (Fin n) (Fin n) A' :=
    (parabolicMatrix R n i).map (algebraMap (ParabolicCoord R n i) A')
  have hg : g.BlockTriangular (parabolicBlock n i) := fun r c h => by
    simp [g, parabolicMatrix_blockTriangular R n i h]
  have hy : IsUnit (g a' a) := IsLocalization.Away.algebraMap_isUnit y
  let x : A' := g a' a' * ↑hy.unit⁻¹
  have hx : x * g a' a = g a' a' := by
    simp only [x, mul_assoc, IsUnit.val_inv_mul, mul_one]
  obtain ⟨hb, hfac⟩ := parabolic_factorization i hi g hg x hx
  have hgdet : IsUnit g.det := isUnit_det_map_ringHom _ (isUnit_det_parabolicMatrix R n i)
  have hbdet : IsUnit (g * Matrix.transvection a a' (-x) *
      permMatrix n (simpleReflection n i hi)).det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transvection_of_ne a a' haa', mul_one]
    exact hgdet.mul (isUnit_det_permMatrix n _)
  have hudet : IsUnit (Matrix.transvection a a' x).det := by
    rw [Matrix.det_transvection_of_ne a a' haa']
    exact isUnit_one
  have hup : (Matrix.transvection a a' x).BlockTriangular id :=
    transvection_blockTriangular (show a < a' by simp [a, a', Fin.lt_def]) x
  let k : GLCoord R n →ₐ[R] A' := (IsScalarTower.toAlgHom R (ParabolicCoord R n i) A').comp
    (Ideal.Quotient.mkₐ R (parabolicIdeal R n i))
  have hk : k = (pairLift (borelPointOfMatrix R _ hbdet hb)
      (borelPointOfMatrix R _ hudet hup)).comp
      (schubertOrbitComorphism R n (simpleReflection n i hi)) := by
    apply glCoord_algHom_ext R
    rw [pointMatrix_pairLift_comp, borelMatrix_map_borelPointOfMatrix,
      borelMatrix_map_borelPointOfMatrix, ← hfac]
    rfl
  have h0 : k f = 0 := by
    rw [hk, AlgHom.comp_apply]
    rw [schubertOrbitIdeal, RingHom.mem_ker] at hf
    change pairLift _ _ ((schubertOrbitComorphism R n (simpleReflection n i hi)).toRingHom f) = 0
    rw [hf, map_zero]
  have hle : Submonoid.powers y ≤ nonZeroDivisors (ParabolicCoord R n i) :=
    Submonoid.powers_le.mpr (parabolicMatrix_mem_nonZeroDivisors R n i hi)
  have hinj : Function.Injective (algebraMap (ParabolicCoord R n i) A') :=
    IsLocalization.injective A' hle
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact hinj (h0.trans (map_zero _).symm)

end FlagVarieties
