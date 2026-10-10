import RSCounterexample.FlagVarieties.PointModel.Sections
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Borel–Weil at the level of sections

For the whole flag variety (`S = Sₙ`, so `π⁻¹ X_S = GL_n`):

* `orbitSet_univ`, `orbitIdeal_univ`: the Bruhat cells cover `GL_n(K)`, and a function of
  `𝒪(GL_n)` vanishing on `GL_n(K)` is zero;
* `borelWeil` (**Borel–Weil, sections**): every `t ∈ 𝒪(GL_n)` with `t(g b) = λ(b) t(g)` lies in the
  flag-minor algebra `A_λ`; that is, `H⁰(G/B, 𝓛(-λ)) = ind_B^G(-λ) = A_λ`;
* `finrank_globalSections`: its dimension is `#chainSet h Sₙ`.

`Γ(X_w, 𝒪) = K` (`GlobalSectionsConstant`) enters, as in the projective normality theorem, as an
explicit hypothesis (the suffix `_of_globalSectionsConstant`); `Normality/Unconditional` discharges
it.
-/

open Schubert Demazure.FlagModule Demazure.SchubertUnions FinPermutation
open GLRep (glEval)

namespace FlagVarieties.PointModel

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

theorem detPoly_ne_zero : genericDetPoly K n ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero (Fin n) K

/-- `K[x_ij] → 𝒪(GL_n)` is injective. -/
theorem algebraMap_coordRing_injective :
    Function.Injective (algebraMap (MatrixEntryPolynomial K n) (GLCoord K n)) :=
  IsLocalization.injective (M := Submonoid.powers (genericDetPoly K n)) (GLCoord K n)
    (powers_le_nonZeroDivisors_of_noZeroDivisors detPoly_ne_zero)

/-- A polynomial vanishing on `GL_n(K)` is zero. -/
theorem eq_zero_of_evalAt_eq_zero [Infinite K] {r : MatrixEntryPolynomial K n}
    (h : ∀ g : GL (Fin n) K, evalAt (g : Matrix (Fin n) (Fin n) K) r = 0) : r = 0 := by
  have h2 : r * genericDetPoly K n = 0 := by
    apply MvPolynomial.funext
    intro x
    let g : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => x (i, j)
    have hev : ∀ p : MatrixEntryPolynomial K n, MvPolynomial.eval x p = evalAt g p := fun _ => rfl
    rw [hev, hev, map_mul, map_zero, evalAt_genericDetPoly]
    by_cases hd : g.det = 0
    · rw [hd, mul_zero]
    · have := h (unitOfDet g (isUnit_iff_ne_zero.mpr hd))
      rw [coe_unitOfDet] at this
      rw [this, zero_mul]
  exact (mul_eq_zero.mp h2).resolve_right detPoly_ne_zero

/-- A function of `𝒪(GL_n)` vanishing at every point of `GL_n(K)` is zero. -/
theorem eq_zero_of_glEval_eq_zero [Infinite K] {t : GLCoord K n}
    (h : ∀ g : GL (Fin n) K, glEval g t = 0) : t = 0 := by
  obtain ⟨r, k, hrk⟩ := exists_mul_det_pow t
  have hr : r = 0 := eq_zero_of_evalAt_eq_zero fun g => by
    have := congrArg (glEval g) hrk
    rw [map_mul, h g, zero_mul, glEval_algebraMap_eq_evalAt] at this
    exact this.symm
  rw [hr, map_zero] at hrk
  have hu : IsUnit (algebraMap (MatrixEntryPolynomial K n) (GLCoord K n)
      (genericDetPoly K n ^ k)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (genericDetPoly K n)).pow k
  exact hu.mul_left_eq_zero.mp hrk

theorem bruhatLower_univ : BruhatLower (Finset.univ : Finset (Equiv.Perm (Fin n))) :=
  fun _ _ _ _ => Finset.mem_univ _

/-- The Bruhat cells cover `GL_n(K)`. -/
theorem orbitSet_univ : orbitSet K (Finset.univ : Finset (Equiv.Perm (Fin n))) = Set.univ :=
  Set.eq_univ_of_forall fun g => by
    obtain ⟨w, hw⟩ := exists_mem_bruhatCell g
    exact mem_orbitSet.mpr ⟨w, Finset.mem_univ _, hw⟩

theorem orbitIdeal_univ [Infinite K] :
    orbitIdeal K (Finset.univ : Finset (Equiv.Perm (Fin n))) = ⊥ := by
  ext t
  rw [mem_orbitIdeal, orbitSet_univ, Ideal.mem_bot]
  constructor
  · intro h
    exact eq_zero_of_glEval_eq_zero fun g => h g (Set.mem_univ g)
  · rintro rfl g _
    exact map_zero _

/-- **Borel–Weil at the level of sections**: a function `t ∈ 𝒪(GL_n)` with `t(g b) = λ(b) t(g)` for
all `g ∈ GL_n(K)`, `b ∈ B` is an element of the flag-minor algebra `A_λ`. -/
theorem borelWeil_of_globalSectionsConstant [IsAlgClosed K] (hSMT : StandardMonomialTheory K)
    (hglobalSections : ∀ w : Equiv.Perm (Fin n), GlobalSectionsConstant K w) (m : ColumnShape n)
    {t : GLCoord K n} (ht : IsSemiInvOn Set.univ (shapeWeightZ m) t) :
    ∃ a ∈ minorSpan K m, t = algebraMap (MatrixEntryPolynomial K n) (GLCoord K n) a := by
  obtain ⟨a, ha, hta⟩ := schubertUnion_normality_of_globalSectionsConstant hSMT hglobalSections m
      bruhatLower_univ t
    (by rwa [orbitSet_univ])
  rw [orbitIdeal_univ, Ideal.mem_bot, sub_eq_zero] at hta
  exact ⟨a, ha, hta⟩

theorem vanishSpan_univ [Infinite K] (m : ColumnShape n) :
    vanishSpan K m (Finset.univ : Finset (Equiv.Perm (Fin n))) = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  rw [mem_vanishSpan, orbitSet_univ] at hp
  exact eq_zero_of_evalAt_eq_zero fun g => hp.2 g (Set.mem_univ g)

/-- `H⁰(G/B, 𝓛(-λ)) = ind_B^G(-λ)` equals the image of `A_λ` in `𝒪(GL_n)`. -/
theorem semiInvSpace_univ_of_globalSectionsConstant [IsAlgClosed K]
    (hSMT : StandardMonomialTheory K)
    (hglobalSections : ∀ w : Equiv.Perm (Fin n), GlobalSectionsConstant K w)
    (m : ColumnShape n) :
    semiInvSpace Set.univ (shapeWeightZ m) =
      (minorSpan K m).map (IsScalarTower.toAlgHom K (MatrixEntryPolynomial K n)
          (GLCoord K n)).toLinearMap := by
  ext t
  constructor
  · intro ht
    obtain ⟨a, ha, rfl⟩ := borelWeil_of_globalSectionsConstant hSMT hglobalSections m ht
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact isSemiInvOn_of_mem_minorSpan ha _

/-- **Dimension of the global sections**: `dim H⁰(G/B, 𝓛(-λ)) = #chainSet h Sₙ`. -/
theorem finrank_globalSections_of_globalSectionsConstant [IsAlgClosed K]
    (hSMT : StandardMonomialTheory K)
    (hglobalSections : ∀ w : Equiv.Perm (Fin n), GlobalSectionsConstant K w) {d : ℕ}
    (h : Fin d → Fin n) :
    Module.finrank K
        (semiInvSpace (Set.univ : Set (GL (Fin n) K)) (shapeWeightZ (columnMultiplicity h))) =
      (chainSet h Finset.univ).card := by
  rw [semiInvSpace_univ_of_globalSectionsConstant hSMT hglobalSections,
      ← (Submodule.equivMapOfInjective _
    (algebraMap_coordRing_injective (K := K) (n := n)) _).finrank_eq]
  have hadd := hSMT.dim h (bruhatLower_univ (n := n))
  rw [vanishSpan_univ, finrank_bot, zero_add, ← minorSpan_columnMultiplicity] at hadd
  exact hadd.symm

end

end FlagVarieties.PointModel
