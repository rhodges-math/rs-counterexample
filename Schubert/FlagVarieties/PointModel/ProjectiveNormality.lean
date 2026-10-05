import Schubert.FlagVarieties.PointModel.UnitIdeal

/-!
# Projective normality of Schubert unions, in ring form

For a Bruhat ideal `S` and a column shape `m` (dominant weight `λ = shapeWeight m`), every function
`t ∈ 𝒪(GL_n)` that is semi-invariant of weight `λ` on `π⁻¹ X_S = orbitSet K S` agrees there with an
element of the flag-minor algebra `A_λ`
(`sectionsGeneratedByMinors_of_bruhatLower_of_globalSectionsConstant`). Together with
`mem_vanishSpan` (the kernel is `I_S^A ∩ A_λ`) this is projective normality: `A_λ ↠ H⁰(X_S, 𝓛(-λ))`.

The proof is a double induction, on the number of non-determinant columns of `m` and on
`#S`:
* `normality_union` (union step, the intersection identity);
* `normality_hyperplane` (hyperplane step, the hyperplane-section identity, the big-cell
  homogenization and the unit ideal);
* `normality_det` (base: only determinant columns), which uses `Γ(X_w, 𝒪) = K` in its
  ring form `GlobalSectionsConstant K w`. `GlobalSectionsConstant` is an explicit hypothesis here
  (the suffix `_of_globalSectionsConstant`); `Normality/Unconditional` discharges it.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation
open GLRep (glEval)

namespace FlagVarieties.PointModel

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {n : ℕ}

/-- **Projective normality** for the column shape `m` and the set `S`: every function semi-invariant
of weight
`shapeWeight m` on `orbitSet K S` agrees there with an element of `A_m`. -/
def SectionsGeneratedByMinors (K : Type*) [Field K] (m : ColumnShape n)
    (S : Finset (Equiv.Perm (Fin n))) : Prop :=
  ∀ t : GLCoord K n, IsSemiInvOn (orbitSet K S) (shapeWeightZ m) t →
    ∃ a ∈ minorSpan K m, t - algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) a ∈ orbitIdeal K S

theorem glEval_sub_algebraMap (g : GL (Fin n) K) (t : GLCoord K n) (a : MatrixEntryPolynomial K n) :
    glEval g (t - algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) a) =
      glEval g t - evalAt (g : Matrix (Fin n) (Fin n) K) a := by
  rw [map_sub, glEval_algebraMap_eq_evalAt]

/-! ### The union step -/

/-- **Union step.** -/
theorem normality_union (hSMT : StandardMonomialTheory K) {m : ColumnShape n}
    {S₁ S₂ : Finset (Equiv.Perm (Fin n))}
    (h₁ : BruhatLower S₁) (h₂ : BruhatLower S₂) (N₁ : SectionsGeneratedByMinors K m S₁)
    (N₂ : SectionsGeneratedByMinors K m S₂) : SectionsGeneratedByMinors K m (S₁ ∪ S₂) := by
  intro t ht
  obtain ⟨a₁, ha₁, hta₁⟩ := N₁ t (ht.mono (orbitSet_mono Finset.subset_union_left))
  obtain ⟨a₂, ha₂, hta₂⟩ := N₂ t (ht.mono (orbitSet_mono Finset.subset_union_right))
  have hdiff : a₁ - a₂ ∈ vanishSpan K m (S₁ ∩ S₂) := by
    rw [mem_vanishSpan]
    refine ⟨Submodule.sub_mem _ ha₁ ha₂, fun g hg => ?_⟩
    have e₁ := mem_orbitIdeal.mp hta₁ g (orbitSet_mono Finset.inter_subset_left hg)
    have e₂ := mem_orbitIdeal.mp hta₂ g (orbitSet_mono Finset.inter_subset_right hg)
    rw [glEval_sub_algebraMap] at e₁ e₂
    rw [map_sub]
    linear_combination e₂ - e₁
  rw [vanishSpan_inter hSMT m h₁ h₂] at hdiff
  obtain ⟨b₁, hb₁, b₂, hb₂, hb⟩ := Submodule.mem_sup.mp hdiff
  refine ⟨a₁ - b₁, Submodule.sub_mem _ ha₁ (mem_vanishSpan.mp hb₁).1, ?_⟩
  rw [mem_orbitIdeal]
  intro g hg
  rw [glEval_sub_algebraMap, map_sub]
  rw [orbitSet_union] at hg
  rcases hg with hg | hg
  · have e₁ := mem_orbitIdeal.mp hta₁ g hg
    rw [glEval_sub_algebraMap] at e₁
    have e₃ := (mem_vanishSpan.mp hb₁).2 g hg
    linear_combination e₁ + e₃
  · have e₂ := mem_orbitIdeal.mp hta₂ g hg
    rw [glEval_sub_algebraMap] at e₂
    have e₄ := (mem_vanishSpan.mp hb₂).2 g hg
    have e₅ := congrArg (evalAt (g : Matrix (Fin n) (Fin n) K)) hb
    rw [map_add, map_sub] at e₅
    linear_combination e₂ - e₄ + e₅

/-! ### Weights -/

theorem shapeWeight_nsmul (N : ℕ) (m : ColumnShape n) :
    shapeWeight (N • m) = N • shapeWeight m := by
  induction N with
  | zero => simp [shapeWeight_zero]
  | succ N ih => rw [succ_nsmul, shapeWeight_add, ih, succ_nsmul]


/-! ### The hyperplane step -/

theorem chartMinor_mem_minorSpan (v : Equiv.Perm (Fin n)) (c : Fin n) :
    chartMinor K v c ∈ minorSpan K (Pi.single c 1) :=
  rowMinor_mem_minorSpan c (leadRows v c)

/-- Raising the exponent of a homogenization. -/
theorem homogenization_pad {v : Equiv.Perm (Fin n)} {Z : Set (GL (Fin n) K)} {m : ColumnShape n}
    {t : GLCoord K n} {N N' : ℕ} (hKK' : N ≤ N') {a : MatrixEntryPolynomial K n}
    (ha : a ∈ minorSpan K (m + N • onesShape n))
    (hav : ∀ g ∈ Z, evalAt (g : Matrix (Fin n) (Fin n) K) a =
      evalAt (g : Matrix (Fin n) (Fin n) K) (chartPoly K v) ^ N * glEval g t) :
    a * chartPoly K v ^ (N' - N) ∈ minorSpan K (m + N' • onesShape n) ∧
      ∀ g ∈ Z, evalAt (g : Matrix (Fin n) (Fin n) K) (a * chartPoly K v ^ (N' - N)) =
        evalAt (g : Matrix (Fin n) (Fin n) K) (chartPoly K v) ^ N' * glEval g t := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hKK'
  rw [Nat.add_sub_cancel_left]
  refine ⟨?_, fun g hg => ?_⟩
  · rw [add_smul, ← add_assoc]
    exact mul_mem_minorSpan ha (pow_mem_minorSpan (chartPoly_mem_minorSpan v) j)
  · rw [map_mul, hav g hg, map_pow, pow_add]
    ring

/-- **Hyperplane step.** The statement for `(m' + ω_k, D_k(w))` and for `(m', ↓w)` gives it
for `(m' + ω_k, ↓w)`. -/
theorem normality_hyperplane [IsAlgClosed K] (hSMT : StandardMonomialTheory K) {m' : ColumnShape n}
    {k : Fin n}
    {w : Equiv.Perm (Fin n)}
    (N_D : SectionsGeneratedByMinors K (m' + Pi.single k 1) (hyperplaneSectionSet k w))
    (N_w : SectionsGeneratedByMinors K m' (lowerSet w)) :
    SectionsGeneratedByMinors K (m' + Pi.single k 1) (lowerSet w) := by
  classical
  intro t ht
  have hDZ : orbitSet K (hyperplaneSectionSet k w) ⊆ orbitSet K (lowerSet w) :=
    orbitSet_mono (hyperplaneSectionSet_subset k w)
  -- (a) the restriction to `D` comes from `A_λ`
  obtain ⟨a₀, ha₀, hta₀⟩ := N_D t (ht.mono hDZ)
  set t₁ := t - algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) a₀ with ht₁def
  have ht₁ : IsSemiInvOn (orbitSet K (lowerSet w)) (shapeWeightZ (m' + Pi.single k 1)) t₁ :=
    ht.sub (isSemiInvOn_of_mem_minorSpan ha₀ _)
  have ht₁D : ∀ g ∈ orbitSet K (hyperplaneSectionSet k w), glEval g t₁ = 0 := mem_orbitIdeal.mp hta₀
  -- (b) homogenization on every big cell, with a common exponent `K₀`
  choose N a ha hav using fun v => exists_homogenization v ht₁
  set K₀ := ∑ v, N v
  have hK : ∀ v, N v ≤ K₀ := fun v => Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ v)
  let a' : Equiv.Perm (Fin n) → MatrixEntryPolynomial K n := fun v =>
      a v * chartPoly K v ^ (K₀ - N v)
  have ha' : ∀ v, a' v ∈ minorSpan K (m' + Pi.single k 1 + K₀ • onesShape n) := fun v =>
    (homogenization_pad (hK v) (ha v) (hav v)).1
  have ha'v : ∀ v, ∀ g ∈ orbitSet K (lowerSet w), evalAt (g : Matrix (Fin n) (Fin n) K) (a' v) =
      evalAt (g : Matrix (Fin n) (Fin n) K) (chartPoly K v) ^ K₀ * glEval g t₁ := fun v =>
    (homogenization_pad (hK v) (ha v) (hav v)).2
  -- (c) the hyperplane-section identity on each chart
  have hshape : m' + Pi.single k 1 + K₀ • onesShape n = m' + K₀ • onesShape n + Pi.single k 1 :=
    add_right_comm _ _ _
  have hH : ∀ v, a' v ∈ vanishSpan K (m' + K₀ • onesShape n + Pi.single k 1) (lowerSet w) ⊔
      (minorSpan K (m' + K₀ • onesShape n)).map (LinearMap.mulLeft K (prefixMinor K w k)) := by
    intro v
    rw [← vanishSpan_hyperplaneSectionSet hSMT, mem_vanishSpan, ← hshape]
    refine ⟨ha' v, fun g hg => ?_⟩
    rw [ha'v v g (hDZ hg), ht₁D g hg, mul_zero]
  choose j hj x hx hjx using fun v => Submodule.mem_sup.mp (hH v)
  choose a'' ha'' hxa using fun v => (Submodule.mem_map.mp (hx v))
  have hjv : ∀ v, ∀ g ∈ orbitSet K (lowerSet w), evalAt (g : Matrix (Fin n) (Fin n) K) (j v) = 0 :=
    fun v => (mem_vanishSpan.mp (hj v)).2
  -- `p a''_v = f_v^{K₀} t₁` on `π⁻¹ X_w`
  have hpa : ∀ v, ∀ g ∈ orbitSet K (lowerSet w),
      evalAt (g : Matrix (Fin n) (Fin n) K) (prefixMinor K w k) *
          evalAt (g : Matrix (Fin n) (Fin n) K) (a'' v) =
        evalAt (g : Matrix (Fin n) (Fin n) K) (chartPoly K v) ^ K₀ * glEval g t₁ := by
    intro v g hg
    have e := congrArg (evalAt (g : Matrix (Fin n) (Fin n) K)) (hjx v)
    rw [← hxa v, LinearMap.mulLeft_apply, map_add, map_mul, hjv v g hg, zero_add,
      ha'v v g hg] at e
    exact e
  -- (d) the overlaps agree, by the nonzerodivisor property of `p`
  have hover : ∀ v v', ∀ g ∈ orbitSet K (lowerSet w),
      evalAt (g : Matrix (Fin n) (Fin n) K) (a'' v) *
          evalAt (g : Matrix (Fin n) (Fin n) K) (chartPoly K v') ^ K₀ =
        evalAt (g : Matrix (Fin n) (Fin n) K) (a'' v') *
          evalAt (g : Matrix (Fin n) (Fin n) K) (chartPoly K v) ^ K₀ := by
    intro v v' g hg
    set e := a'' v * chartPoly K v' ^ K₀ - a'' v' * chartPoly K v ^ K₀ with he
    have hemem : e ∈ minorSpan K (m' + K₀ • onesShape n + K₀ • onesShape n) :=
      Submodule.sub_mem _ (mul_mem_minorSpan (ha'' v) (pow_mem_minorSpan
        (chartPoly_mem_minorSpan v') K₀)) (mul_mem_minorSpan (ha'' v') (pow_mem_minorSpan
        (chartPoly_mem_minorSpan v) K₀))
    have hpe : prefixMinor K w k * e ∈
        vanishSpan K (m' + K₀ • onesShape n + K₀ • onesShape n + Pi.single k 1) (lowerSet w) := by
      rw [mem_vanishSpan]
      refine ⟨prefixMinor_mul_mem_minorSpan w k hemem, fun g' hg' => ?_⟩
      rw [he, map_mul, map_sub, map_mul, map_mul, map_pow, map_pow, mul_sub, ← mul_assoc,
        ← mul_assoc, hpa v g' hg', hpa v' g' hg']
      ring
    have := (mem_vanishSpan.mp (mem_vanishSpan_of_prefixMinor_mul hSMT hemem hpe)).2 g hg
    rw [he, map_sub, map_mul, map_mul, map_pow, map_pow, sub_eq_zero] at this
    exact this
  -- (e) gluing with a partition of unity
  obtain ⟨c, hc⟩ := exists_partition_of_unity (K := K) (n := n) (K₀ + 1)
  set t' : GLCoord K n := ∑ v, c v *
    algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (a'' v * chartPoly K v) with ht'def
  have hval : ∀ g ∈ orbitSet K (lowerSet w), ∀ v₀,
      evalAt (g : Matrix (Fin n) (Fin n) K) (chartPoly K v₀) ≠ 0 →
        glEval g t' = evalAt (g : Matrix (Fin n) (Fin n) K) (a'' v₀) /
          evalAt (g : Matrix (Fin n) (Fin n) K) (chartPoly K v₀) ^ K₀ := by
    intro g hg v₀ hv₀
    set τ := evalAt (g : Matrix (Fin n) (Fin n) K) (a'' v₀) /
      evalAt (g : Matrix (Fin n) (Fin n) K) (chartPoly K v₀) ^ K₀
    have hterm : ∀ v, evalAt (g : Matrix (Fin n) (Fin n) K) (a'' v * chartPoly K v) =
        evalAt (g : Matrix (Fin n) (Fin n) K) (chartPoly K v) ^ (K₀ + 1) * τ := by
      intro v
      have h := hover v v₀ g hg
      have hpow : evalAt (g : Matrix (Fin n) (Fin n) K) (chartPoly K v₀) ^ K₀ ≠ 0 :=
        pow_ne_zero _ hv₀
      rw [map_mul, mul_div_assoc', eq_div_iff hpow]
      linear_combination (evalAt (g : Matrix (Fin n) (Fin n) K) (chartPoly K v)) * h
    have h1 := congrArg (glEval g) hc
    rw [map_sum, map_one] at h1
    rw [ht'def, map_sum]
    calc ∑ v, glEval g (c v * algebraMap (MatrixEntryPolynomial K n) (GLCoord K n)
        (a'' v * chartPoly K v))
        = ∑ v, glEval g (c v * algebraMap (MatrixEntryPolynomial K n) (GLCoord K n)
            (chartPoly K v) ^ (K₀ + 1))
            * τ := by
          refine Finset.sum_congr rfl fun v _ => ?_
          have e1 : glEval g (c v * algebraMap (MatrixEntryPolynomial K n) (GLCoord K n)
              (a'' v * chartPoly K v)) =
              glEval g (c v) * evalAt (g : Matrix (Fin n) (Fin n) K) (a'' v * chartPoly K v) := by
            rw [map_mul (glEval g), glEval_algebraMap_eq_evalAt]
          have e2 :
              glEval g (c v * algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (chartPoly K v) ^
                  (K₀ + 1)) =
              glEval g (c v) * evalAt (g : Matrix (Fin n) (Fin n) K) (chartPoly K v) ^
                  (K₀ + 1) := by
            rw [map_mul (glEval g), map_pow, glEval_algebraMap_eq_evalAt]
          rw [e1, e2, hterm v]
          ring
      _ = τ := by rw [← Finset.sum_mul, h1, one_mul]
  -- (f) `t'` is semi-invariant of weight `λ - ω_k` and `p t' = t₁` on `π⁻¹ X_w`
  have ht' : IsSemiInvOn (orbitSet K (lowerSet w)) (shapeWeightZ m') t' := by
    intro g hg b hb
    obtain ⟨v₀, hv₀⟩ := exists_chartPoly_ne_zero g
    have hbd := diag_ne_zero_of_isBorel hb
    have hbu : (b : Matrix (Fin n) (Fin n) K).IsUpperTriangular := hb
    have hfb := evalAt_mul_of_mem_minorSpan (chartPoly_mem_minorSpan v₀) (g : Matrix _ _ K)
      (b : Matrix _ _ K) hbu
    have hab := evalAt_mul_of_mem_minorSpan (ha'' v₀) (g : Matrix _ _ K) (b : Matrix _ _ K) hbu
    have hv₀b :
        evalAt ((g * b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (chartPoly K v₀) ≠ 0 := by
      rw [Units.val_mul, hfb]
      exact mul_ne_zero (diagPow_ne_zero hbd _) hv₀
    rw [hval (g * b) (orbitSet_mul_borel hg hb) v₀ hv₀b, hval g hg v₀ hv₀, Units.val_mul, hfb, hab,
      borelCharValue_shapeWeightZ, shapeWeight_add, diagPow_add, shapeWeight_nsmul, diagPow_nsmul]
    have hd := diagPow_ne_zero hbd (shapeWeight (onesShape n))
    rw [mul_pow]
    field_simp
  have hpt' : ∀ g ∈ orbitSet K (lowerSet w),
      evalAt (g : Matrix (Fin n) (Fin n) K) (prefixMinor K w k) * glEval g t' = glEval g t₁ := by
    intro g hg
    obtain ⟨v₀, hv₀⟩ := exists_chartPoly_ne_zero g
    rw [hval g hg v₀ hv₀, mul_div_assoc', hpa v₀ g hg]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ hv₀)
  -- (g) induction on the weight
  obtain ⟨a₁, ha₁, hta₁⟩ := N_w t' ht'
  refine ⟨a₀ + prefixMinor K w k * a₁,
    Submodule.add_mem _ ha₀ (prefixMinor_mul_mem_minorSpan w k ha₁), ?_⟩
  rw [mem_orbitIdeal]
  intro g hg
  have e₁ := mem_orbitIdeal.mp hta₁ g hg
  rw [glEval_sub_algebraMap] at e₁
  have e₂ := hpt' g hg
  rw [ht₁def, glEval_sub_algebraMap] at e₂
  rw [glEval_sub_algebraMap, map_add, map_mul]
  linear_combination evalAt (g : Matrix (Fin n) (Fin n) K) (prefixMinor K w k) * e₁ - e₂

/-! ### The base: determinant columns only -/

/-- The number of columns of `m` of height `< n` (non-determinant columns). -/
def nonDeterminantColumnCount (m : ColumnShape n) : ℕ := ∑ k, if k.val + 1 < n then m k else 0

theorem nonDeterminantColumnCount_add_single (m : ColumnShape n) (k : Fin n) (hk : k.val + 1 < n) :
    nonDeterminantColumnCount (m + Pi.single k 1) = nonDeterminantColumnCount m + 1 := by
  classical
  unfold nonDeterminantColumnCount
  have hterm : ∀ i : Fin n, (if i.val + 1 < n then (m + Pi.single k 1 : ColumnShape n) i else 0) =
      (if i.val + 1 < n then m i else 0) + (if i = k then 1 else 0) := by
    intro i
    by_cases hi : i = k
    · subst hi
      simp [hk]
    · simp [hi]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem flagRowMinor_last_eq_detPoly (k : Fin n) (hk : k.val + 1 = n) :
    rowMinor K k (prefixIndex k) = genericDetPoly K n := by
  rw [rowMinor]
  have : (Matrix.of fun i j : Fin (k.val + 1) =>
      (MvPolynomial.X (prefixIndex k i, prefixIndex k j) : MatrixEntryPolynomial K n)) =
      (Matrix.mvPolynomialX (Fin n) (Fin n) K).submatrix (finCongr hk) (finCongr hk) := by
    ext i j
    rfl
  rw [this, Matrix.det_submatrix_equiv_self]

theorem chartMinor_one_last (k : Fin n) (hk : k.val + 1 = n) :
    chartMinor K (1 : Equiv.Perm (Fin n)) k = genericDetPoly K n := by
  rw [chartMinor, ← flagRowMinor_last_eq_detPoly k hk]
  rfl

theorem isUnit_chartExtremal_of_nonDeterminantColumnCount {m : ColumnShape n}
    (hm : nonDeterminantColumnCount m = 0) :
    IsUnit (algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) (chartExtremal K 1 m)) := by
  rw [chartExtremal, map_prod]
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun k _ => ?_
  rw [map_pow]
  by_cases hk : k.val + 1 < n
  · have : m k = 0 := by
      have h := (Finset.sum_eq_zero_iff.mp hm) k (Finset.mem_univ k)
      simpa [hk] using h
    rw [this, pow_zero]
    exact isUnit_one
  · rw [chartMinor_one_last k (by have := k.isLt; omega)]
    exact (IsLocalization.Away.algebraMap_isUnit (genericDetPoly K n)).pow _

/-- **Base of the induction**: only determinant columns. The weight is a power of `det`, so the
statement reduces to `Γ(X_w, 𝒪) = K`. -/
theorem normality_det_of_globalSectionsConstant {m : ColumnShape n}
    (hm : nonDeterminantColumnCount m = 0) {w : Equiv.Perm (Fin n)}
    (hglobalSections : GlobalSectionsConstant K w) : SectionsGeneratedByMinors K m
        (lowerSet w) := by
  intro t ht
  set D := chartExtremal K (1 : Equiv.Perm (Fin n)) m
  have hDunit : IsUnit (algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) D) :=
    isUnit_chartExtremal_of_nonDeterminantColumnCount hm
  have hD := chartExtremal_mem_minorSpan (K := K) (1 : Equiv.Perm (Fin n)) m
  have hDne : ∀ g : GL (Fin n) K, evalAt (g : Matrix (Fin n) (Fin n) K) D ≠ 0 := by
    intro g h
    have h2 := hDunit.map (glEval g)
    rw [glEval_algebraMap_eq_evalAt, h] at h2
    exact not_isUnit_zero h2
  obtain ⟨u, hu⟩ := hDunit
  set t' := t * ↑u⁻¹ with ht'def
  have hevt' : ∀ g : GL (Fin n) K, glEval g t' * evalAt (g : Matrix (Fin n) (Fin n) K) D =
      glEval g t := by
    intro g
    rw [ht'def, ← glEval_algebraMap_eq_evalAt, ← hu, ← map_mul, mul_assoc, Units.inv_mul, mul_one]
  have ht' : IsSemiInvOn (orbitSet K (lowerSet w)) 0 t' := by
    intro g hg b hb
    have h1 := hevt' (g * b)
    have h2 := hevt' g
    have hbu : (b : Matrix (Fin n) (Fin n) K).IsUpperTriangular := hb
    have hDb := evalAt_mul_of_mem_minorSpan hD (g : Matrix _ _ K) (b : Matrix _ _ K) hbu
    rw [ht g hg b hb, Units.val_mul, hDb, borelCharValue_shapeWeightZ] at h1
    have hd := diagPow_ne_zero (diag_ne_zero_of_isBorel hb) (shapeWeight m)
    have hg0 := hDne g
    have hc : borelCharValue (0 : Fin n → ℤ) (b : Matrix (Fin n) (Fin n) K) = 1 := by
        simp [borelCharValue]
    rw [hc, one_mul]
    have : (glEval (g * b) t' - glEval g t') * (diagPow (shapeWeight m) (b : Matrix _ _ K) *
        evalAt (g : Matrix _ _ K) D) = 0 := by
      rw [← h2] at h1
      linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (mul_ne_zero hd hg0)
  obtain ⟨γ, hγ⟩ := hglobalSections t' ht'
  refine ⟨γ • D, Submodule.smul_mem _ γ hD, ?_⟩
  rw [mem_orbitIdeal]
  intro g hg
  have e := mem_orbitIdeal.mp hγ g hg
  rw [map_sub, AlgHom.commutes] at e
  rw [glEval_sub_algebraMap, map_smul, smul_eq_mul, ← hevt' g]
  have : glEval g t' = γ := by
    have := sub_eq_zero.mp e
    simpa using this
  rw [this]
  ring

/-! ### The induction -/

theorem bruhatLower_erase_of_maximal {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S)
    {w : Equiv.Perm (Fin n)} (hmax : ∀ u ∈ S, w ≤ᴮ u → u = w) : BruhatLower (S.erase w) := by
  intro u hu v hvu
  rw [Finset.mem_erase] at hu ⊢
  refine ⟨fun hvw => hu.1 ?_, hS u hu.2 v hvu⟩
  subst hvw
  exact hmax u hu.2 hvu

theorem lowerSet_subset {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S)
    {w : Equiv.Perm (Fin n)} (hw : w ∈ S) : lowerSet w ⊆ S := fun v hv =>
  hS w hw v (mem_lowerSet.mp hv)

/-- **Projective normality** (ring form), with `GlobalSectionsConstant` as an explicit hypothesis.
-/
theorem sectionsGeneratedByMinors_of_bruhatLower_of_globalSectionsConstant [IsAlgClosed K]
    (hSMT : StandardMonomialTheory K)
    (hglobalSections : ∀ w : Equiv.Perm (Fin n), GlobalSectionsConstant K w) :
    ∀ (N : ℕ) (m : ColumnShape n), nonDeterminantColumnCount m = N →
      ∀ S : Finset (Equiv.Perm (Fin n)), BruhatLower S → SectionsGeneratedByMinors K m S := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
  intro m hmN S
  induction S using Finset.strongInduction with
  | H S ihS =>
  intro hS
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · intro t _
    exact ⟨0, Submodule.zero_mem _, by
      rw [mem_orbitIdeal]
      intro g hg
      simp [orbitSet] at hg⟩
  obtain ⟨w, hwS, hwmax⟩ := Finset.exists_max_image S (fun w => (lowerSet w).card) hne
  have hmax : ∀ u ∈ S, w ≤ᴮ u → u = w := by
    intro u hu hwu
    by_contra hne'
    have hsub : lowerSet w ⊂ lowerSet u := by
      refine (Finset.ssubset_iff_of_subset fun v hv =>
        mem_lowerSet.mpr (strongBruhat_trans (mem_lowerSet.mp hv) hwu)).mpr
          ⟨u, mem_lowerSet_self u, fun hu' => hne' ?_⟩
      exact strongBruhat_antisymm (mem_lowerSet.mp hu') hwu
    exact absurd (hwmax u hu) (not_le.mpr (Finset.card_lt_card hsub))
  have hlow := lowerSet_subset hS hwS
  by_cases hprin : S ⊆ lowerSet w
  · -- the principal case `S = ↓w`
    have hSeq : S = lowerSet w := Finset.Subset.antisymm hprin hlow
    subst hSeq
    by_cases hN : N = 0
    · exact normality_det_of_globalSectionsConstant (hmN.trans hN) (hglobalSections w)
    · -- choose a non-determinant column
      have hpos : nonDeterminantColumnCount m ≠ 0 := hmN ▸ hN
      obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
      have hkn : k.val + 1 < n := by
        by_contra h
        exact hk (ite_eq_right h)
      have hmk : m k ≠ 0 := by
        intro h
        exact hk (by rw [ite_eq_left hkn, h])
      set m' := m - Pi.single k 1
      have hm : m = m' + Pi.single k 1 := by
        funext i
        by_cases hi : i = k
        · subst hi
          simp only [m', Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
          omega
        · simp [m', hi]
      have hm'N : nonDeterminantColumnCount m' < N := by
        have := nonDeterminantColumnCount_add_single m' k hkn
        rw [← hm] at this
        omega
      rw [hm]
      refine normality_hyperplane hSMT ?_ (ihN _ hm'N m' rfl _ (bruhatLower_lowerSet w))
      rw [← hm]
      exact ihS _ ((Finset.ssubset_iff_of_subset (hyperplaneSectionSet_subset k w)).mpr
        ⟨w, mem_lowerSet_self w, self_notMem_hyperplaneSectionSet k w⟩)
            (bruhatLower_hyperplaneSectionSet k w)
  · -- the union step
    have hS' := bruhatLower_erase_of_maximal hS hmax
    have hunion : S = lowerSet w ∪ S.erase w := by
      ext x
      simp only [Finset.mem_union, Finset.mem_erase]
      constructor
      · intro hx
        by_cases hxw : x = w
        · exact Or.inl (hxw ▸ mem_lowerSet_self w)
        · exact Or.inr ⟨hxw, hx⟩
      · rintro (hx | ⟨-, hx⟩)
        · exact hlow hx
        · exact hx
    rw [hunion]
    refine normality_union hSMT (bruhatLower_lowerSet w) hS' ?_ ?_
    · exact ihS _ ((Finset.ssubset_iff_of_subset hlow).mpr (by
        obtain ⟨x, hx, hxw⟩ := Finset.not_subset.mp hprin
        exact ⟨x, hx, hxw⟩)) (bruhatLower_lowerSet w)
    · exact ihS _ (Finset.erase_ssubset hwS) hS'

/-- **Projective normality**, ring form. Let `S` be a Bruhat ideal and `m` a column
shape, of weight `λ = shapeWeight m`. Assume `Γ(X_w, 𝒪) = K` for every `w`. Then every
`t ∈ 𝒪(GL_n)` semi-invariant of weight `λ` on `π⁻¹ X_S` agrees there with an element of the
flag-minor algebra `A_λ`. -/
theorem schubertUnion_normality_of_globalSectionsConstant [IsAlgClosed K]
    (hSMT : StandardMonomialTheory K)
    (hglobalSections : ∀ w : Equiv.Perm (Fin n), GlobalSectionsConstant K w)
    (m : ColumnShape n) {S : Finset (Equiv.Perm (Fin n))} (hS : BruhatLower S) (t : GLCoord K n)
    (ht : IsSemiInvOn (orbitSet K S) (shapeWeightZ m) t) :
    ∃ a ∈ minorSpan K m, t - algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) a ∈
        orbitIdeal K S :=
  sectionsGeneratedByMinors_of_bruhatLower_of_globalSectionsConstant hSMT hglobalSections _ m rfl S
      hS t ht

end

end FlagVarieties.PointModel
