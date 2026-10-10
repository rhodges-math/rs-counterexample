import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedUniversalRestrictionCoherence

/-!
# Transport of coordinate sheaf morphisms

Canonical restriction comparisons give functorial transport of
morphisms between coordinate free sheaves. On open immersions this equals
transport by pullback, and transport along an isomorphism is injective.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {X Y Z : Scheme.{u}} {n d e : ℕ}

/-- A coordinate morphism transported by pullback and the original free comparisons. -/
def coordinatePullbackMap (f : X ⟶ Y)
    (q : coordinateFreeSheaf Y n ⟶ coordinateFreeSheaf Y d) :
    coordinateFreeSheaf X n ⟶ coordinateFreeSheaf X d :=
  (coordinatePullbackFreeIso f n).inv ≫ (Scheme.Modules.pullback f).map q ≫
    (coordinatePullbackFreeIso f d).hom

/-- A coordinate morphism transported by restriction. -/
def coordinateRestrictMap (f : X ⟶ Y) [IsOpenImmersion f]
    (q : coordinateFreeSheaf Y n ⟶ coordinateFreeSheaf Y d) :
    coordinateFreeSheaf X n ⟶ coordinateFreeSheaf X d :=
  (coordinateRestrictFreeIso f n).inv ≫ (Scheme.Modules.restrictFunctor f).map q ≫
    (coordinateRestrictFreeIso f d).hom

/-- Restriction transport is the pullback transport on every open immersion. -/
theorem coordinateRestrictMap_eq_pullback (f : X ⟶ Y) [IsOpenImmersion f]
    (q : coordinateFreeSheaf Y n ⟶ coordinateFreeSheaf Y d) :
    coordinateRestrictMap f q = coordinatePullbackMap f q := by
  unfold coordinateRestrictMap coordinatePullbackMap
  rw [← coordinateRestrictionIso_eq, ← coordinateRestrictionIso_eq,
    ← coordinatePullbackIso_eq, ← coordinatePullbackIso_eq]
  simp only [coordinateRestrictionIso, Iso.trans_inv, Iso.trans_hom, Iso.app_hom,
    Iso.app_inv, Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.restrictFunctor f).map q)
    ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app _) _,
    (Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- Transport respects composition of module sheaf morphisms. -/
theorem coordinateRestrictMap_comp (f : X ⟶ Y) [IsOpenImmersion f]
    (q : coordinateFreeSheaf Y n ⟶ coordinateFreeSheaf Y d)
    (t : coordinateFreeSheaf Y d ⟶ coordinateFreeSheaf Y e) :
    coordinateRestrictMap f (q ≫ t) = coordinateRestrictMap f q ≫ coordinateRestrictMap f t := by
  simp only [coordinateRestrictMap, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- Transport at the identity scheme morphism fixes the morphism. -/
theorem coordinateRestrictMap_id (q : coordinateFreeSheaf X n ⟶ coordinateFreeSheaf X d) :
    coordinateRestrictMap (𝟙 X) q = q := by
  unfold coordinateRestrictMap
  rw [coordinateRestrictFreeIso_id, coordinateRestrictFreeIso_id]
  simp only [Iso.app_hom, Iso.app_inv]
  rw [Scheme.Modules.restrictFunctorId.hom.naturality]
  simp

/-- Transport is functorial in composition of open immersions. -/
theorem coordinateRestrictMap_comp_scheme (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g]
    (q : coordinateFreeSheaf Z n ⟶ coordinateFreeSheaf Z d) :
    coordinateRestrictMap f (coordinateRestrictMap g q) = coordinateRestrictMap (f ≫ g) q := by
  let α := Scheme.Modules.restrictFunctorComp f g
  calc
    coordinateRestrictMap f (coordinateRestrictMap g q) =
        (coordinateRestrictFreeIso (f ≫ g) n).inv ≫
          α.hom.app (coordinateFreeSheaf Z n) ≫
          (Scheme.Modules.restrictFunctor f).map ((Scheme.Modules.restrictFunctor g).map q) ≫
          (Scheme.Modules.restrictFunctor f).map (coordinateRestrictFreeIso g d).hom ≫
          (coordinateRestrictFreeIso f d).hom := by
      apply (cancel_epi (coordinateRestrictFreeIso (f ≫ g) n).hom).mp
      conv_lhs => rw [← coordinateRestrictFreeIso_comp f g n]
      simp only [coordinateRestrictMap, Functor.map_comp, Category.assoc,
        Iso.hom_inv_id_assoc, Iso.hom_inv_id_map_assoc]
      rfl
    _ = (coordinateRestrictFreeIso (f ≫ g) n).inv ≫
          (Scheme.Modules.restrictFunctor (f ≫ g)).map q ≫
          α.hom.app (coordinateFreeSheaf Z d) ≫
          (Scheme.Modules.restrictFunctor f).map (coordinateRestrictFreeIso g d).hom ≫
          (coordinateRestrictFreeIso f d).hom := by
      have h := α.hom.naturality q
      change (Scheme.Modules.restrictFunctor (f ≫ g)).map q ≫ α.hom.app _ =
        α.hom.app _ ≫ (Scheme.Modules.restrictFunctor f).map
          ((Scheme.Modules.restrictFunctor g).map q) at h
      simpa only [Category.assoc] using congrArg
        (fun t => (coordinateRestrictFreeIso (f ≫ g) n).inv ≫ t ≫
          (Scheme.Modules.restrictFunctor f).map (coordinateRestrictFreeIso g d).hom ≫
          (coordinateRestrictFreeIso f d).hom) h.symm
    _ = coordinateRestrictMap (f ≫ g) q := by
      rw [coordinateRestrictFreeIso_comp]
      rfl

/-- The composition identity also holds for pullback transport along
the open immersions used by the universal chart construction. -/
theorem coordinatePullbackMap_comp_open (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g]
    (q : coordinateFreeSheaf Z n ⟶ coordinateFreeSheaf Z d) :
    coordinatePullbackMap f (coordinatePullbackMap g q) = coordinatePullbackMap (f ≫ g) q := by
  simp only [← coordinateRestrictMap_eq_pullback]
  exact coordinateRestrictMap_comp_scheme f g q

/-- Transport through a scheme isomorphism has the inverse transport as a left inverse. -/
theorem coordinateRestrictMap_iso_left_inverse (f : X ⟶ Y) [IsIso f]
    (q : coordinateFreeSheaf Y n ⟶ coordinateFreeSheaf Y d) :
    coordinateRestrictMap (inv f) (coordinateRestrictMap f q) = q := by
  rw [coordinateRestrictMap_comp_scheme]
  simp only [IsIso.inv_hom_id, coordinateRestrictMap_id]

/-- Equality after transport to an isomorphic scheme implies equality of the original morphisms. -/
theorem coordinateRestrictMap_injective (f : X ⟶ Y) [IsIso f] :
    Function.Injective (coordinateRestrictMap f (n := n) (d := d)) := by
  intro q t h
  have hh := congrArg (coordinateRestrictMap (inv f)) h
  simpa only [coordinateRestrictMap_iso_left_inverse] using hh

/-- A target isomorphism transports to a coordinate target isomorphism. -/
def coordinateRestrictIso (f : X ⟶ Y) [IsOpenImmersion f]
    (t : coordinateFreeSheaf Y n ≅ coordinateFreeSheaf Y d) :
    coordinateFreeSheaf X n ≅ coordinateFreeSheaf X d :=
  (coordinateRestrictFreeIso f n).symm ≪≫ (Scheme.Modules.restrictFunctor f).mapIso t ≪≫
    coordinateRestrictFreeIso f d

end FlagVarieties.Foundations.QuotientCharts
