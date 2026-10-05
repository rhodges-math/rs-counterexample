import Schubert.FlagVarieties.Foundations.Schemes.AffineCoordinateQuotientBaseChangeSource

/-!
# Normalization of the affine free-source comparison

The adjunction-derived affine tilde comparison must agree with the
generator-labelled free-sheaf pullback comparison used by the quotient charts.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.AffineTildePullback

open AlgebraicGeometry CategoryTheory

universe u

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The sheaf base-change isomorphism is normalized by the units of the two
adjunctions, including the scalar-action comparison on top sections. -/
theorem baseChangeNatIso_unit (M : ModuleCat.{u} R) :
    (sheafAdjunction φ).unit.app M ≫
        ((Scheme.Modules.pushforward (specMap φ) ⋙
          moduleSpecΓFunctor (R := R))).map ((baseChangeNatIso φ).hom.app M) ≫
        (rightAdjunctionIso φ).hom.app
          ((ModuleCat.extendScalars φ.hom ⋙ tilde.functor S).obj M) =
      (moduleAdjunction φ).unit.app M := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (sheafAdjunction φ)
    ((moduleAdjunction φ).ofNatIsoRight (rightAdjunctionIso φ).symm) M
  have h' := congrArg (fun t => t ≫ (rightAdjunctionIso φ).hom.app
      ((ModuleCat.extendScalars φ.hom ⋙ tilde.functor S).obj M)) h
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom] at h'
  have hcancel := congrArg (fun t => t.app
      ((ModuleCat.extendScalars φ.hom ⋙ tilde.functor S).obj M))
    (Iso.inv_hom_id (rightAdjunctionIso φ))
  simp only [NatTrans.comp_app, NatTrans.id_app] at hcancel
  simp only [Category.assoc, hcancel] at h'
  exact h'.trans (Category.comp_id _)

/-- The affine comparison takes the original top section `m` to the section
represented by `1 ⊗ m` in the scalar extension. -/
theorem baseChangeNatIso_top (M : ModuleCat.{u} R) (m : M) :
    ((baseChangeNatIso φ).hom.app M).app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction (specMap φ)).unit.app
          (tilde M)).app ⊤ ((tilde.toOpen M ⊤) m)) =
      (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤)
        ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M m) := by
  have h := congrArg (fun (t : M ⟶
      (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).obj
        ((ModuleCat.extendScalars φ.hom ⋙ tilde.functor S).obj M)) => t m)
    (baseChangeNatIso_unit φ M)
  simp only [ModuleCat.hom_comp] at h
  exact h

/-- Scalar extension of the coefficient ring as a module, with the
coefficient homomorphism determining the tensor product. -/
def extendedScalarIso :
    (ModuleCat.extendScalars φ.hom).obj (ModuleCat.of R R) ≅
      ModuleCat.of S S := by
  letI : Algebra R S := φ.hom.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso

set_option linter.style.haveILetI false in
theorem extendedScalarIso_unit :
    (extendedScalarIso φ).hom
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app
        (ModuleCat.of R R) (1 : R)) = (1 : S) := by
  letI : Algebra R S := φ.hom.toAlgebra
  change (TensorProduct.AlgebraTensorModule.rid R S S)
    ((1 : S) ⊗ₜ[R] (1 : R)) = (1 : S)
  simp

theorem tildeSelf_top_one (A : CommRingCat.{u}) :
    (tilde.toOpen (ModuleCat.of A A) ⊤) (1 : A) =
      (1 : Γ(Spec A, ⊤)) := by
  change (algebraMap A Γ(Spec A, ⊤)) 1 = 1
  simp

theorem tildeMap_top_apply {M N : ModuleCat.{u} S} (g : M ⟶ N) (m : M) :
    (tilde.map g).app ⊤ ((tilde.toOpen M ⊤) m) =
      (tilde.toOpen N ⊤) (g m) := by
  have h := ConcreteCategory.congr_hom (tilde.toOpen_map_app g ⊤) m
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  change (tilde.map g).app ⊤ ((tilde.toOpen M ⊤) m) =
    (tilde.toOpen N ⊤) (g m) at h
  exact h

/-- The canonical structure-sheaf pullback takes the pulled-back global unit
to the global unit. -/
theorem quotientPullbackUnitIso_top_one :
    ((FlagVarieties.Foundations.QuotientPair.quotientPullbackUnitIso (specMap φ)).hom).app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction (specMap φ)).unit.app
        (tilde (ModuleCat.of R R))).app ⊤ (1 : Γ(Spec R, ⊤))) =
      (1 : Γ(Spec S, ⊤)) := by
  have hu := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    (specMap φ).toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at hu
  have h := congrArg
    (fun (t : FlagVarieties.Foundations.QuotientPair.unitSheaf (Spec R) ⟶
        (Scheme.Modules.pushforward (specMap φ)).obj
          (FlagVarieties.Foundations.QuotientPair.unitSheaf (Spec S))) =>
      t.app ⊤ (1 : Γ(Spec R, ⊤))) hu
  change ((FlagVarieties.Foundations.QuotientPair.quotientPullbackUnitIso (specMap φ)).hom).app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction (specMap φ)).unit.app
        (tilde (ModuleCat.of R R))).app ⊤ (1 : Γ(Spec R, ⊤))) =
    (specMap φ).app ⊤ (1 : Γ(Spec R, ⊤)) at h
  simpa only [map_one] using h

/-- On the coefficient module, the adjunction comparison is the canonical
pullback of the structure sheaf. -/
theorem baseChangeScalarIso_eq :
    (baseChangeIso φ (ModuleCat.of R R)).hom ≫
        tilde.map (extendedScalarIso φ).hom =
      (FlagVarieties.Foundations.QuotientPair.quotientPullbackUnitIso (specMap φ)).hom := by
  apply ((sheafAdjunction φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [Adjunction.homEquiv_unit, Functor.map_comp,
    sheafAdjunction, Adjunction.comp_unit_app, ModuleCat.hom_comp]
  simp only [LinearMap.comp_apply]
  change (tilde.map (extendedScalarIso φ).hom).app ⊤
      (((baseChangeIso φ (ModuleCat.of R R)).hom).app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction (specMap φ)).unit.app
          (tilde (ModuleCat.of R R))).app ⊤
            ((tilde.toOpen (ModuleCat.of R R) ⊤) (1 : R)))) =
    ((FlagVarieties.Foundations.QuotientPair.quotientPullbackUnitIso (specMap φ)).hom).app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction (specMap φ)).unit.app
        (tilde (ModuleCat.of R R))).app ⊤
          ((tilde.toOpen (ModuleCat.of R R) ⊤) (1 : R)))
  rw [tildeSelf_top_one R]
  rw [quotientPullbackUnitIso_top_one φ]
  have h := baseChangeNatIso_top φ (ModuleCat.of R R) (1 : R)
  rw [tildeSelf_top_one R] at h
  change ((baseChangeIso φ (ModuleCat.of R R)).hom).app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction (specMap φ)).unit.app
        (tilde (ModuleCat.of R R))).app ⊤ (1 : Γ(Spec R, ⊤))) =
      (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj (ModuleCat.of R R)) ⊤)
        ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app
          (ModuleCat.of R R) (1 : R)) at h
  rw [h]
  rw [tildeMap_top_apply]
  rw [extendedScalarIso_unit]
  exact tildeSelf_top_one S

end FlagVarieties.Foundations.AffineTildePullback

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

universe u

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- The scalar tensor identification in the same algebra instance as the
coordinate tensor identification. -/
def coordinateExtendedScalarIso :
    (ModuleCat.extendScalars (algebraMap R B)).obj (ModuleCat.of R R) ≅
      ModuleCat.of B B :=
  eqToIso (coordinateExtendScalarsObjEq R B (ModuleCat.of R R)) ≪≫
    (TensorProduct.AlgebraTensorModule.rid R B B).toModuleIso

theorem coordinateExtendedScalarIso_eq :
    coordinateExtendedScalarIso R B =
      AffineTildePullback.extendedScalarIso
        (CommRingCat.ofHom (algebraMap R B)) := by
  have h : (algebraMap R B).toAlgebra = inferInstanceAs (Algebra R B) :=
    toAlgebra_algebraMap
  rw [← h]
  rfl

/-- Scalar extension carries each old standard coordinate inclusion to the
identically labelled new inclusion. -/
theorem coordinateExtendedSingle_source {n : ℕ} (i : Fin n) :
    (ModuleCat.extendScalars (algebraMap R B)).map
        (ModuleCat.ofHom (LinearMap.single R (fun _ : Fin n => R) i)) ≫
      (coordinateExtendedFreeIso R B (n := n)).hom =
    (coordinateExtendedScalarIso R B).hom ≫
      ModuleCat.ofHom (LinearMap.single B (fun _ : Fin n => B) i) := by
  unfold coordinateExtendedFreeIso coordinateExtendedScalarIso
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, coordinateExtendScalarsMapEq]
  simp only [Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  change (coordinateTensorFreeEquiv R B (n := n)).toLinearMap.comp
      ((LinearMap.single R (fun _ : Fin n => R) i).baseChange B) =
    (LinearMap.single B (fun _ : Fin n => B) i).comp
      (TensorProduct.AlgebraTensorModule.rid R B B).toLinearMap
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b r =>
      ext j
      simp [coordinateTensorFreeEquiv, LinearMap.comp_apply,
        LinearMap.baseChange_tmul, TensorProduct.piScalarRightHom_tmul,
        TensorProduct.AlgebraTensorModule.rid_tmul, Pi.single_apply]
  | add x y hx hy => simpa only [map_add, Pi.single_add] using congrArg₂ (· + ·) hx hy

theorem coordinateTildeFreePullbackIso_generator {n : ℕ} (i : Fin n) :
    (Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
        (tilde.map (ModuleCat.ofHom
          (LinearMap.single R (fun _ : Fin n => R) i))) ≫
      (coordinateTildeFreePullbackIso R B (n := n)).hom ≫
      (coordinateTildeFreeIso (CommRingCat.of B) n).hom =
    (FlagVarieties.Foundations.QuotientPair.quotientPullbackUnitIso
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))).hom ≫
      SheafOfModules.ιFree (⟨i⟩ : CoordinateIndex.{u} n) := by
  simp only [coordinateTildeFreePullbackIso, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
        (tilde.map (ModuleCat.ofHom
          (LinearMap.single R (fun _ : Fin n => R) i)))),
    AffineTildePullback.baseChangeIso_map]
  simp only [tilde.functor]
  have hpair :
      (tilde.functor (CommRingCat.of B)).map
        ((ModuleCat.extendScalars (algebraMap R B)).map
          (ModuleCat.ofHom (LinearMap.single R (fun _ : Fin n => R) i))) ≫
        (tilde.functor (CommRingCat.of B)).map
          (coordinateExtendedFreeIso R B (n := n)).hom =
      (tilde.functor (CommRingCat.of B)).map
        (coordinateExtendedScalarIso R B).hom ≫
        (tilde.functor (CommRingCat.of B)).map (ModuleCat.ofHom
          (LinearMap.single B (fun _ : Fin n => B) i)) := by
    rw [← Functor.map_comp, coordinateExtendedSingle_source, Functor.map_comp]
  simp only [CommRingCat.hom_ofHom, tilde.functor] at hpair ⊢
  have hpush := congrArg (fun t =>
      (AffineTildePullback.baseChangeIso
        (CommRingCat.ofHom (algebraMap R B)) (ModuleCat.of R R)).hom ≫
        t ≫ (coordinateTildeFreeIso (CommRingCat.of B) n).hom) hpair
  calc
    _ = (AffineTildePullback.baseChangeIso
        (CommRingCat.ofHom (algebraMap R B)) (ModuleCat.of R R)).hom ≫
          (tilde.map (coordinateExtendedScalarIso R B).hom ≫
            tilde.map (ModuleCat.ofHom
              (LinearMap.single B (fun _ : Fin n => B) i))) ≫
          (coordinateTildeFreeIso (CommRingCat.of B) n).hom := by
            simpa only [Category.assoc] using hpush
    _ = (FlagVarieties.Foundations.QuotientPair.quotientPullbackUnitIso
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))).hom ≫
      SheafOfModules.ιFree (⟨i⟩ : CoordinateIndex.{u} n) := by
        simp only [Category.assoc]
        rw [coordinateTildeFreeIso_generator]
        simp only [← Category.assoc]
        rw [coordinateExtendedScalarIso_eq,
          AffineTildePullback.baseChangeScalarIso_eq]
  trace_state

/-- The adjunction-derived ambient source comparison agrees with Mathlib's
canonical labelled free-sheaf pullback comparison. -/
theorem coordinateTildeFreePullbackIso_normalized {n : ℕ} :
    (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
          (coordinateTildeFreeIso (CommRingCat.of R) n).hom ≫
      (coordinatePullbackFreeIso
        (Spec.map (CommRingCat.ofHom (algebraMap R B))) n).hom =
    (coordinateTildeFreePullbackIso R B (n := n)).hom ≫
      (coordinateTildeFreeIso (CommRingCat.of B) n).hom := by
  apply (cancel_epi ((Scheme.Modules.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
      (coordinateTildeFreeIso (CommRingCat.of R) n).inv)).mp
  apply Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))) _ _
      (SheafOfModules.isColimitFreeCofan
        (R := (Spec (CommRingCat.of R)).ringCatSheaf) (CoordinateIndex.{u} n)))
  intro i
  rcases i with ⟨i⟩
  change (Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
        (SheafOfModules.ιFree (⟨i⟩ : CoordinateIndex.{u} n)) ≫
      (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
          (coordinateTildeFreeIso (CommRingCat.of R) n).inv ≫
        (Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
            (coordinateTildeFreeIso (CommRingCat.of R) n).hom ≫
          (coordinatePullbackFreeIso
            (Spec.map (CommRingCat.ofHom (algebraMap R B))) n).hom =
    (Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
        (SheafOfModules.ιFree (⟨i⟩ : CoordinateIndex.{u} n)) ≫
      (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
          (coordinateTildeFreeIso (CommRingCat.of R) n).inv ≫
        (coordinateTildeFreePullbackIso R B (n := n)).hom ≫
          (coordinateTildeFreeIso (CommRingCat.of B) n).hom
  have hgen :
      SheafOfModules.ιFree (⟨i⟩ : CoordinateIndex.{u} n) ≫
        (coordinateTildeFreeIso (CommRingCat.of R) n).inv =
      tilde.map (ModuleCat.ofHom
        (LinearMap.single R (fun _ : Fin n => R) i)) := by
    rw [← coordinateTildeFreeIso_generator]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hpgen :
      (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
          (SheafOfModules.ιFree (⟨i⟩ : CoordinateIndex.{u} n)) ≫
        (Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
            (coordinateTildeFreeIso (CommRingCat.of R) n).inv =
      (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
          (tilde.map (ModuleCat.ofHom
            (LinearMap.single R (fun _ : Fin n => R) i))) := by
    rw [← Functor.map_comp, hgen]
  have hcancel :
      (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
          (coordinateTildeFreeIso (CommRingCat.of R) n).inv ≫
        (Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
            (coordinateTildeFreeIso (CommRingCat.of R) n).hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id]
    exact (Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map_id _
  have hfirst := congrArg (fun t =>
      (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
          (SheafOfModules.ιFree (⟨i⟩ : CoordinateIndex.{u} n)) ≫
        t ≫ (coordinatePullbackFreeIso
          (Spec.map (CommRingCat.ofHom (algebraMap R B))) n).hom) hcancel
  calc
    _ = (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
          (SheafOfModules.ιFree (⟨i⟩ : CoordinateIndex.{u} n)) ≫
        (coordinatePullbackFreeIso
          (Spec.map (CommRingCat.ofHom (algebraMap R B))) n).hom := by
            simpa only [Category.assoc, Category.id_comp] using hfirst
    _ = (FlagVarieties.Foundations.QuotientPair.quotientPullbackUnitIso
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))).hom ≫
          SheafOfModules.ιFree (⟨i⟩ : CoordinateIndex.{u} n) :=
      coordinatePullbackIso_generator _ _
    _ = (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
          (tilde.map (ModuleCat.ofHom
            (LinearMap.single R (fun _ : Fin n => R) i))) ≫
        (coordinateTildeFreePullbackIso R B (n := n)).hom ≫
          (coordinateTildeFreeIso (CommRingCat.of B) n).hom :=
      (coordinateTildeFreePullbackIso_generator R B i).symm
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun t => t ≫ (coordinateTildeFreePullbackIso R B (n := n)).hom ≫
          (coordinateTildeFreeIso (CommRingCat.of B) n).hom) hpgen.symm

end FlagVarieties.Foundations.QuotientCharts
