import RSCounterexample.FlagVarieties.LineBundle.Restriction

/-!
# Comparison of `i^* 𝓛(η)` with `𝓛_X(η)`

For a closed subscheme `X ⊆ Flₙ` with closed immersion `i`, the comparison
`i^* 𝓛(η) ⟶ 𝓛_X(η)` (restriction of semi-invariant functions from `π⁻¹(V)` to `π⁻¹(V) ∩ P_X`) is an
isomorphism (`FlagVarieties.isIso_lineBundleComparison`). Over `X ∩ bigCell v` both sides are
free of rank one: `𝓛_X(η)` on the restriction of the basis `τ_η` (descent along the local section
of `P_X ⟶ X`), and `i^* 𝓛(η)` because `𝓛(η)` is invertible; the comparison sends the pullback of
the basis section of `𝓛(η)` to the basis section of `𝓛_X(η)`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

variable (R : Type u) [CommRing R] (n : ℕ) (I : (FlagScheme R n).IdealSheafData)
  (η : Fin n → ℤ)

/-- The basis section of `𝓛_X(η)` over `X ∩ bigCell v`. -/
def lineBundleXSection (v : Equiv.Perm (Fin n)) : Γ(lineBundleX R n I η, bigCellX R n I v) :=
  (((preimageHom R n I).semiInvariantSheafMap η).app (bigCell R v)).hom
    (lineBundleBigCellSection R n η v)

theorem lineBundleXSection_ι (v : Equiv.Perm (Fin n)) :
    (show Γ((preimageAction R n I).P, (preimageAction R n I).q ⁻¹ᵁ bigCellX R n I v) from
      (((preimageAction R n I).semiInvariantι η).app (bigCellX R n I v)).hom
        (lineBundleXSection R n I η v)) =
      ((preimageHom R n I).pullbackSections (bigCell R v)).hom
        ((bigCellTwistUnit R v η : (Γ(GLScheme R n, FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v))ˣ) :
          Γ(GLScheme R n, FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v)) := by
  have h := congrArg (fun g => (g.app (bigCell R v)).hom (lineBundleBigCellSection R n η v))
    ((preimageHom R n I).semiInvariantSheafMap_ι η)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at h
  refine h.trans ?_
  exact congrArg ((preimageHom R n I).directImageMap.app (bigCell R v)).hom
    (lineBundleι_bigCellSection R n η v)

theorem isUnit_lineBundleXSection_ι (v : Equiv.Perm (Fin n)) :
    IsUnit (show Γ((preimageAction R n I).P, (preimageAction R n I).q ⁻¹ᵁ bigCellX R n I v) from
      (((preimageAction R n I).semiInvariantι η).app (bigCellX R n I v)).hom
        (lineBundleXSection R n I η v)) := by
  rw [lineBundleXSection_ι]
  exact (Units.isUnit (bigCellTwistUnit R v η)).map _

/-- On `X ∩ bigCell v`, every section of `𝓛_X(η)` is uniquely a multiple of the basis section. -/
theorem bijective_smul_lineBundleXSection (v : Equiv.Perm (Fin n)) {W : I.subscheme.Opens}
    (hW : W ≤ bigCellX R n I v) :
    Function.Bijective (fun a : Γ(I.subscheme, W) =>
      a • ((lineBundleX R n I η).presheaf.map (homOfLE hW).op).hom
        (lineBundleXSection R n I η v)) :=
  (preimageLocalData R n I v).bijective_smul_section_of_isUnit η hW _
    (isUnit_lineBundleXSection_ι R n I η v)

/-- The pullback `i^* s_v` of the basis section of `𝓛(η)` over the big cell. -/
def pulledBigCellSection (v : Equiv.Perm (Fin n)) :
    Γ((Scheme.Modules.pullback I.subschemeι).obj (lineBundle R n η), bigCellX R n I v) :=
  ((((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app
    (lineBundle R n η)).app (bigCell R v)).hom (lineBundleBigCellSection R n η v))

theorem lineBundleComparison_pulledBigCellSection (v : Equiv.Perm (Fin n)) :
    ((lineBundleComparison R n I η).app (bigCellX R n I v)).hom
        (pulledBigCellSection R n I η v) = lineBundleXSection R n I η v :=
  (preimageHom R n I).pullbackSemiInvariantSheafMap_app_pullbackSection η (bigCell R v) _

/-- For a free rank-one trivialization `e` of `M` over `U`, every section over `W ⊆ U` is uniquely
a multiple of the restricted basis section. -/
theorem bijective_smul_trivializationGenerator {X : Scheme.{u}} (M : X.Modules) {U W : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) (h : W ≤ U) :
    Function.Bijective (fun a : Γ(X, W) =>
      a • (M.presheaf.map (homOfLE h).op).hom (Scheme.Modules.trivializationGenerator M e)) := by
  let c := Scheme.Modules.trivializationCoordinate M e (homOfLE h)
  have hc : c ((M.presheaf.map (homOfLE h).op).hom (Scheme.Modules.trivializationGenerator M e)) =
      1 :=
    Scheme.Modules.trivializationCoordinate_map_trivializationGenerator M e (homOfLE h)
  have hf : (fun a : Γ(X, W) =>
      a • (M.presheaf.map (homOfLE h).op).hom (Scheme.Modules.trivializationGenerator M e)) =
      c.symm := by
    funext a
    apply c.injective
    rw [LinearEquiv.apply_symm_apply, map_smul, hc, smul_eq_mul, mul_one]
  rw [hf]
  exact c.symm.bijective

/-- **`i^* 𝓛(η) ≅ 𝓛_X(η)`.** -/
theorem isIso_lineBundleComparison : IsIso (lineBundleComparison R n I η) := by
  have : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible (FlagScheme R n)
      (lineBundle R n η) := isInvertible_lineBundle R n η
  let M := (Scheme.Modules.pullback I.subschemeι).obj (lineBundle R n η)
  have : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible I.subscheme M :=
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_pullback I.subschemeι _
  let t := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible M
  have ht : ⨆ k, t.X k = ⊤ := ((Opens.coversTop_iff _ t.X).mp t.coversTop)
  refine isIso_of_forall_bijective _ (ι := ULift.{u} (Equiv.Perm (Fin n)) × t.I)
    (fun k => bigCellX R n I k.1.down ⊓ t.X k.2) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨v, hv⟩ := exists_mem_bigCell R (I.subschemeι x)
    have hx : x ∈ ⨆ k, t.X k := by rw [ht]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(⟨v⟩, k), hv, hk⟩
  · rintro ⟨⟨v⟩, k⟩ W hW
    have hW1 : W ≤ bigCellX R n I v := hW.trans inf_le_left
    have hW2 : W ≤ t.X k := hW.trans inf_le_right
    let Φ := lineBundleComparison R n I η
    let ΦW : Γ(M, W) →ₗ[Γ(I.subscheme, W)] Γ(lineBundleX R n I η, W) :=
      { toFun := (Φ.app W).hom
        map_add' := map_add _
        map_smul' := fun a x => Scheme.Modules.Hom.app_smul Φ a x }
    refine bijective_of_bases ΦW ((M.presheaf.map (homOfLE hW1).op).hom
      (pulledBigCellSection R n I η v))
      (bijective_smul_trivializationGenerator M (t.iso k) hW2)
      (bijective_smul_lineBundleXSection R n I η v hW1) ?_
    change (Φ.app W).hom ((M.presheaf.map (homOfLE hW1).op).hom
      (pulledBigCellSection R n I η v)) = _
    have h := ConcreteCategory.congr_hom (Φ.mapPresheaf.naturality (homOfLE hW1).op)
      (pulledBigCellSection R n I η v)
    change (Φ.app W).hom ((M.presheaf.map _).hom _) =
      ((lineBundleX R n I η).presheaf.map _).hom ((Φ.app _).hom _) at h
    rw [h, lineBundleComparison_pulledBigCellSection]

end FlagVarieties
