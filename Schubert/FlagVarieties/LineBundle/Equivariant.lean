import Schubert.FlagVarieties.LineBundle.Sections

/-!
# Semi-invariant functions and equivariant morphisms

For a scheme `P` over `T` with a right action of `B` (`FlagVarieties.BorelAction`):

* `BorelAction.IsSemiInvariant E η f`: a function `f` on `q⁻¹(W)` satisfies `f(x b) = η(b)⁻¹ f(x)`,
  i.e. `a^* f = pr₂^* η⁻¹ · pr₁^* f`;
* `BorelAction.mem_range_semiInvariantι_app_iff`: the sections of `semiInvariantSheaf E η` over `W`
  are exactly the semi-invariant functions on `q⁻¹(W)`;
* `BorelAction.Hom`: an equivariant morphism `j : P' ⟶ P` over a morphism of bases `i : T' ⟶ T`;
  pulling back along `j` preserves semi-invariance (`BorelAction.Hom.isSemiInvariant_pullback`).
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace BorelAction

variable {R : Type u} [CommRing R] {n : ℕ} {T : Scheme.{u}} (E : BorelAction R n T)

theorem actionFst_preimage_le (W : T.Opens) : E.actionFst ⁻¹ᵁ E.q ⁻¹ᵁ W ≤ E.act ⁻¹ᵁ E.q ⁻¹ᵁ W :=
  (E.preimage_actionFst_q W).le

/-- The function `pr₂^* η⁻¹`, restricted to an open of `P ×_R B`. -/
def twistOn (η : Fin n → ℤ) (W : E.actionDomain.Opens) : Γ(E.actionDomain, W) :=
  (E.actionDomain.presheaf.map (homOfLE le_top).op).hom (E.twist η)

/-- `pr₂^* η⁻¹` on an open, as the pullback along `pr₂` of the function `η⁻¹` on `B`. -/
theorem twistOn_eq (η : Fin n → ℤ) (W : E.actionDomain.Opens) :
    E.twistOn η W = (E.actionSnd.appLE ⊤ W (by simp)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (BorelCoord R n))).inv
        (((borelCharacterUnit R n η)⁻¹ : (BorelCoord R n)ˣ) : BorelCoord R n)) :=
  rfl

theorem twistOn_map (η : Fin n → ℤ) {W W' : E.actionDomain.Opens} (h : W' ≤ W) :
    (E.actionDomain.presheaf.map (homOfLE h).op).hom (E.twistOn η W) = E.twistOn η W' := by
  rw [twistOn, twistOn, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- **Semi-invariant functions**: `f` on `q⁻¹(W)` with `f(x b) = η(b)⁻¹ f(x)`, i.e.
`a^* f = pr₂^* η⁻¹ · pr₁^* f`. -/
def IsSemiInvariant (η : Fin n → ℤ) {W : T.Opens} (f : Γ(E.P, E.q ⁻¹ᵁ W)) : Prop :=
  (E.act.appLE (E.q ⁻¹ᵁ W) (E.actionFst ⁻¹ᵁ E.q ⁻¹ᵁ W) (E.actionFst_preimage_le W)).hom f =
    E.twistOn η _ * (E.actionFst.app (E.q ⁻¹ᵁ W)).hom f

/-- The sections of the semi-invariant sheaf over `W` are the semi-invariant functions on
`q⁻¹(W)`. -/
theorem mem_range_semiInvariantι_app_iff (η : Fin n → ℤ) (W : T.Opens)
    (f : Γ(E.directImage, W)) :
    f ∈ Set.range ((E.semiInvariantι η).app W).hom ↔ E.IsSemiInvariant η (W := W) f := by
  refine (mem_range_kernel_ι_app_iff (E.pullbackAct - E.pullbackTwist η) W f).trans ?_
  refine (sub_eq_zero (a := (E.pullbackAct.app W).hom f)
    (b := ((E.pullbackTwist η).app W).hom f)).trans ?_
  exact Eq.congr (E.pullbackAct_app W f) (E.pullbackTwist_app η W f)

/-- Semi-invariance is preserved by restriction to a smaller open. -/
theorem IsSemiInvariant.map {η : Fin n → ℤ} {W W' : T.Opens} (h : W' ≤ W)
    {f : Γ(E.P, E.q ⁻¹ᵁ W)} (hf : E.IsSemiInvariant η f) :
    E.IsSemiInvariant η (W := W')
      ((E.P.presheaf.map (homOfLE (E.q.preimage_mono h)).op).hom f) := by
  unfold IsSemiInvariant at hf ⊢
  have e1 : (E.act.appLE (E.q ⁻¹ᵁ W') (E.actionFst ⁻¹ᵁ E.q ⁻¹ᵁ W') (E.actionFst_preimage_le W')).hom
      ((E.P.presheaf.map (homOfLE (E.q.preimage_mono h)).op).hom f) =
      (E.actionDomain.presheaf.map
          (homOfLE (E.actionFst.preimage_mono (E.q.preimage_mono h))).op).hom
        ((E.act.appLE (E.q ⁻¹ᵁ W) (E.actionFst ⁻¹ᵁ E.q ⁻¹ᵁ W) (E.actionFst_preimage_le W)).hom
            f) := by
    change (E.P.presheaf.map _ ≫ E.act.appLE _ _ _).hom f =
      (E.act.appLE _ _ _ ≫ E.actionDomain.presheaf.map _).hom f
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  have e2 : (E.actionFst.app (E.q ⁻¹ᵁ W')).hom
      ((E.P.presheaf.map (homOfLE (E.q.preimage_mono h)).op).hom f) =
      (E.actionDomain.presheaf.map
          (homOfLE (E.actionFst.preimage_mono (E.q.preimage_mono h))).op).hom
        ((E.actionFst.app (E.q ⁻¹ᵁ W)).hom f) := by
    change (E.P.presheaf.map _ ≫ E.actionFst.app _).hom f =
        (E.actionFst.app _ ≫ E.actionDomain.presheaf.map _).hom f
    rw [Scheme.Hom.naturality]
    rfl
  rw [e1, e2, hf, map_mul, twistOn_map]

theorem semiInvariantι_condition (η : Fin n → ℤ) :
    E.semiInvariantι η ≫ (E.pullbackAct - E.pullbackTwist η) = 0 :=
  kernel.condition _

/-- `appLE` only depends on the morphism, not on the proof of the inclusion of opens. -/
theorem _root_.FlagVarieties.appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    {U : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V e' := by
  subst h
  rfl

/-- `(f ≫ g)^* = f^* ∘ g^*` on functions. -/
theorem _root_.FlagVarieties.appLE_comp_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {U : Z.Opens} {V : Y.Opens} {W : X.Opens} (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V)
    (e : W ≤ (f ≫ g) ⁻¹ᵁ U) (x : Γ(Z, U)) :
    ((f ≫ g).appLE U W e).hom x = (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

variable {E} in
/-- An equivariant morphism `j : P' ⟶ P` of `B`-schemes over a morphism of bases `i : T' ⟶ T`. -/
structure Hom {T' : Scheme.{u}} (E' : BorelAction R n T') (E : BorelAction R n T)
    (i : T' ⟶ T) where
  /-- The morphism of total spaces. -/
  j : E'.P ⟶ E.P
  j_q : j ≫ E.q = E'.q ≫ i
  j_toSpec : j ≫ E.toSpec = E'.toSpec
  act_j : E'.act ≫ j = pullback.map _ _ _ _ j (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, j_toSpec]) (by simp) ≫ E.act

namespace Hom

variable {E} {T' : Scheme.{u}} {E' : BorelAction R n T'} {i : T' ⟶ T} (φ : Hom E' E i)

/-- `j × id : P' ×_R B ⟶ P ×_R B`. -/
def prodMap : E'.actionDomain ⟶ E.actionDomain :=
  pullback.map _ _ _ _ φ.j (𝟙 _) (𝟙 _) (by rw [Category.comp_id, φ.j_toSpec]) (by simp)

@[reassoc (attr := simp)] theorem prodMap_actionFst : φ.prodMap ≫ E.actionFst = E'.actionFst ≫
    φ.j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem prodMap_actionSnd : φ.prodMap ≫ E.actionSnd = E'.actionSnd := by
  simp [prodMap]

theorem act_j' : E'.act ≫ φ.j = φ.prodMap ≫ E.act :=
  φ.act_j

theorem preimage_le (W : T.Opens) : E'.q ⁻¹ᵁ i ⁻¹ᵁ W ≤ φ.j ⁻¹ᵁ E.q ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, φ.j_q]

theorem prodMap_preimage_le (W : T.Opens) :
    E'.actionFst ⁻¹ᵁ E'.q ⁻¹ᵁ i ⁻¹ᵁ W ≤ φ.prodMap ⁻¹ᵁ E.actionFst ⁻¹ᵁ E.q ⁻¹ᵁ W := by
  have h : E'.actionFst ≫ E'.q ≫ i = φ.prodMap ≫ E.actionFst ≫ E.q := by
    rw [prodMap_actionFst_assoc, φ.j_q]
  exact (congrArg (fun f => f ⁻¹ᵁ W) h).le

/-- Pulling back functions along `j`, `f ↦ j^* f`. -/
def pullbackSections (W : T.Opens) : Γ(E.P, E.q ⁻¹ᵁ W) ⟶ Γ(E'.P, E'.q ⁻¹ᵁ i ⁻¹ᵁ W) :=
  φ.j.appLE _ _ (φ.preimage_le W)

theorem prodMap_twistOn (η : Fin n → ℤ) {W : E.actionDomain.Opens} {W' : E'.actionDomain.Opens}
    (h : W' ≤ φ.prodMap ⁻¹ᵁ W) :
    (φ.prodMap.appLE W W' h).hom (E.twistOn η W) = E'.twistOn η W' := by
  rw [twistOn_eq, twistOn_eq]
  refine (appLE_comp_apply φ.prodMap E.actionSnd _ h (by simp) _).symm.trans ?_
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (appLE_eq_of_eq φ.prodMap_actionSnd _ _)) _

/-- `j^*` commutes with `pr₁^*`. -/
theorem prodMap_actionFst_app (W : T.Opens) (f : Γ(E.P, E.q ⁻¹ᵁ W)) :
    (φ.prodMap.appLE _ _ (φ.prodMap_preimage_le W)).hom ((E.actionFst.app (E.q ⁻¹ᵁ W)).hom f) =
      (E'.actionFst.app (E'.q ⁻¹ᵁ i ⁻¹ᵁ W)).hom ((φ.pullbackSections W).hom f) := by
  have hle : E'.actionFst ⁻¹ᵁ E'.q ⁻¹ᵁ i ⁻¹ᵁ W ≤ (φ.prodMap ≫ E.actionFst) ⁻¹ᵁ E.q ⁻¹ᵁ W :=
    φ.prodMap_preimage_le W
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
  refine (appLE_comp_apply φ.prodMap E.actionFst le_rfl (φ.prodMap_preimage_le W) hle f).symm.trans
      ?_
  rw [DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (appLE_eq_of_eq φ.prodMap_actionFst hle
    ((φ.prodMap_actionFst ▸ hle)))) f]
  exact appLE_comp_apply E'.actionFst φ.j (φ.preimage_le W) le_rfl _ f

/-- **Pulling back along an equivariant morphism preserves semi-invariance.** -/
theorem isSemiInvariant_pullbackSections {η : Fin n → ℤ} {W : T.Opens} {f : Γ(E.P, E.q ⁻¹ᵁ W)}
    (hf : E.IsSemiInvariant η f) :
    E'.IsSemiInvariant η (W := i ⁻¹ᵁ W) ((φ.pullbackSections W).hom f) := by
  unfold IsSemiInvariant at hf ⊢
  have hle₁ : E'.actionFst ⁻¹ᵁ E'.q ⁻¹ᵁ i ⁻¹ᵁ W ≤ (E'.act ≫ φ.j) ⁻¹ᵁ E.q ⁻¹ᵁ W :=
    (E'.actionFst_preimage_le (i ⁻¹ᵁ W)).trans (E'.act.preimage_mono (φ.preimage_le W))
  have hle₂ : E'.actionFst ⁻¹ᵁ E'.q ⁻¹ᵁ i ⁻¹ᵁ W ≤ (φ.prodMap ≫ E.act) ⁻¹ᵁ E.q ⁻¹ᵁ W :=
    (φ.prodMap_preimage_le W).trans (φ.prodMap.preimage_mono (E.actionFst_preimage_le W))
  calc (E'.act.appLE _ _ (E'.actionFst_preimage_le (i ⁻¹ᵁ W))).hom ((φ.pullbackSections W).hom f)
      = ((E'.act ≫ φ.j).appLE (E.q ⁻¹ᵁ W) _ hle₁).hom f :=
        (appLE_comp_apply E'.act φ.j (φ.preimage_le W) _ hle₁ f).symm
    _ = ((φ.prodMap ≫ E.act).appLE (E.q ⁻¹ᵁ W) _ hle₂).hom f :=
        DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (appLE_eq_of_eq φ.act_j' hle₁ hle₂)) f
    _ = (φ.prodMap.appLE _ _ (φ.prodMap_preimage_le W)).hom
          ((E.act.appLE _ _ (E.actionFst_preimage_le W)).hom f) :=
        appLE_comp_apply φ.prodMap E.act _ _ hle₂ f
    _ = _ := by
        rw [hf, map_mul, φ.prodMap_twistOn, φ.prodMap_actionFst_app]

/-- `j^*` commutes with the action maps: `(j × id)^* a^* = a'^* j^*`. -/
theorem act_pullbackSections (W : T.Opens) (f : Γ(E.P, E.q ⁻¹ᵁ W)) :
    (E'.act.appLE _ _ (E'.actionFst_preimage_le (i ⁻¹ᵁ W))).hom ((φ.pullbackSections W).hom f) =
      (φ.prodMap.appLE _ _ (φ.prodMap_preimage_le W)).hom
        ((E.act.appLE _ _ (E.actionFst_preimage_le W)).hom f) := by
  have hle₁ : E'.actionFst ⁻¹ᵁ E'.q ⁻¹ᵁ i ⁻¹ᵁ W ≤ (E'.act ≫ φ.j) ⁻¹ᵁ E.q ⁻¹ᵁ W :=
    (E'.actionFst_preimage_le (i ⁻¹ᵁ W)).trans (E'.act.preimage_mono (φ.preimage_le W))
  have hle₂ : E'.actionFst ⁻¹ᵁ E'.q ⁻¹ᵁ i ⁻¹ᵁ W ≤ (φ.prodMap ≫ E.act) ⁻¹ᵁ E.q ⁻¹ᵁ W :=
    (φ.prodMap_preimage_le W).trans (φ.prodMap.preimage_mono (E.actionFst_preimage_le W))
  exact (appLE_comp_apply E'.act φ.j (φ.preimage_le W) _ hle₁ f).symm.trans
    ((DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (appLE_eq_of_eq φ.act_j' hle₁ hle₂)) f).trans
      (appLE_comp_apply φ.prodMap E.act _ _ hle₂ f))

/-- `f ↦ j^* f`, as a morphism `q_* 𝒪_P ⟶ i_* q'_* 𝒪_{P'}`. -/
def directImageMap : E.directImage ⟶ (Scheme.Modules.pushforward i).obj E'.directImage :=
  (Scheme.Modules.pushforward E.q).map
      (SheafOfModules.unitToPushforwardObjUnit φ.j.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp φ.j E.q).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr φ.j_q).hom.app _ ≫
    (Scheme.Modules.pushforwardComp E'.q i).inv.app _

theorem directImageMap_app (W : T.Opens) (f : Γ(E.P, E.q ⁻¹ᵁ W)) :
    (φ.directImageMap.app W).hom f = (φ.pullbackSections W).hom f :=
  rfl

theorem prodMap_comp_q : φ.prodMap ≫ E.actionFst ≫ E.q = (E'.actionFst ≫ E'.q) ≫ i := by
  rw [prodMap_actionFst_assoc, φ.j_q, Category.assoc]

/-- `g ↦ (j × id)^* g`, as a morphism `(q ∘ pr₁)_* 𝒪 ⟶ i_* (q' ∘ pr₁)_* 𝒪`. -/
def directImageProdMap :
    E.directImageProd ⟶ (Scheme.Modules.pushforward i).obj E'.directImageProd :=
  (Scheme.Modules.pushforward (E.actionFst ≫ E.q)).map
      (SheafOfModules.unitToPushforwardObjUnit φ.prodMap.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp φ.prodMap (E.actionFst ≫ E.q)).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr φ.prodMap_comp_q).hom.app _ ≫
    (Scheme.Modules.pushforwardComp (E'.actionFst ≫ E'.q) i).inv.app _

theorem directImageProdMap_app (W : T.Opens) (g : Γ(E.actionDomain, E.actionFst ⁻¹ᵁ E.q ⁻¹ᵁ W)) :
    (φ.directImageProdMap.app W).hom g = (φ.prodMap.appLE _ _ (φ.prodMap_preimage_le W)).hom g :=
  rfl

theorem directImageMap_pullbackAct :
    φ.directImageMap ≫ (Scheme.Modules.pushforward i).map E'.pullbackAct =
      E.pullbackAct ≫ φ.directImageProdMap := by
  apply Scheme.Modules.hom_ext
  intro W
  ext x
  exact (E'.pullbackAct_app (i ⁻¹ᵁ W) ((φ.pullbackSections W).hom x)).trans
    ((φ.act_pullbackSections W x).trans
      (congrArg (φ.prodMap.appLE _ _ (φ.prodMap_preimage_le W)).hom (E.pullbackAct_app W x).symm))

theorem directImageMap_pullbackTwist (η : Fin n → ℤ) :
    φ.directImageMap ≫ (Scheme.Modules.pushforward i).map (E'.pullbackTwist η) =
      E.pullbackTwist η ≫ φ.directImageProdMap := by
  apply Scheme.Modules.hom_ext
  intro W
  ext x
  refine (E'.pullbackTwist_app η (i ⁻¹ᵁ W) ((φ.pullbackSections W).hom x)).trans ?_
  refine Eq.trans ?_
    (congrArg (φ.prodMap.appLE _ _ (φ.prodMap_preimage_le W)).hom (E.pullbackTwist_app η W x).symm)
  refine Eq.trans ?_ (map_mul (φ.prodMap.appLE _ _ (φ.prodMap_preimage_le W)).hom _ _).symm
  exact congrArg₂ (· * ·) (φ.prodMap_twistOn η _).symm (φ.prodMap_actionFst_app W x).symm

theorem directImageMap_comp (η : Fin n → ℤ) :
    φ.directImageMap ≫ (Scheme.Modules.pushforward i).map (E'.pullbackAct - E'.pullbackTwist η) =
      (E.pullbackAct - E.pullbackTwist η) ≫ φ.directImageProdMap := by
  rw [Functor.map_sub, Preadditive.comp_sub, Preadditive.sub_comp, directImageMap_pullbackAct,
    directImageMap_pullbackTwist]

/-- **The comparison `𝓛_T(η) ⟶ i_* 𝓛_{T'}(η)`**: restriction of semi-invariant functions along
the equivariant morphism `j`. -/
def semiInvariantSheafMap (η : Fin n → ℤ) :
    E.semiInvariantSheaf η ⟶ (Scheme.Modules.pushforward i).obj (E'.semiInvariantSheaf η) :=
  kernel.lift ((Scheme.Modules.pushforward i).map (E'.pullbackAct - E'.pullbackTwist η))
      (E.semiInvariantι η ≫ φ.directImageMap) (by
        rw [Category.assoc, φ.directImageMap_comp, ← Category.assoc, E.semiInvariantι_condition,
          zero_comp]) ≫
    (PreservesKernel.iso (Scheme.Modules.pushforward i) _).inv

@[reassoc]
theorem semiInvariantSheafMap_ι (η : Fin n → ℤ) :
    φ.semiInvariantSheafMap η ≫ (Scheme.Modules.pushforward i).map (E'.semiInvariantι η) =
      E.semiInvariantι η ≫ φ.directImageMap := by
  show (kernel.lift _ _ _ ≫ (PreservesKernel.iso _ _).inv) ≫
      (Scheme.Modules.pushforward i).map (kernel.ι _) = E.semiInvariantι η ≫ φ.directImageMap
  rw [Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι]

/-- The comparison `i^* 𝓛_T(η) ⟶ 𝓛_{T'}(η)`, adjoint to `semiInvariantSheafMap`. -/
def pullbackSemiInvariantSheafMap (η : Fin n → ℤ) :
    (Scheme.Modules.pullback i).obj (E.semiInvariantSheaf η) ⟶ E'.semiInvariantSheaf η :=
  ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm (φ.semiInvariantSheafMap η)

/-- On the pullback `i^* s` of a section `s` of `𝓛_T(η)`, the comparison is restriction of
functions along `j`. -/
theorem pullbackSemiInvariantSheafMap_app_pullbackSection (η : Fin n → ℤ) (U : T.Opens)
    (s : Γ(E.semiInvariantSheaf η, U)) :
    ((φ.pullbackSemiInvariantSheafMap η).app (i ⁻¹ᵁ U)).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _).app U).hom s) =
      ((φ.semiInvariantSheafMap η).app U).hom s := by
  have h := ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).apply_symm_apply
    (φ.semiInvariantSheafMap η)
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun g => (g.app U).hom s) h

end Hom


end BorelAction

end FlagVarieties
