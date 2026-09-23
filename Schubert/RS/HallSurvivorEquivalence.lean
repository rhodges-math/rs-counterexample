import Schubert.RS.HallHeightFamilies
import Schubert.RS.HallOneEastWeight

/-! A weight-preserving bijection retains every nonintersecting Hall family. -/

namespace Schubert.RS.HallLattice
noncomputable section
variable {d M : ℕ} (y : Fin d → Fin (M+1))

abbrev StrictHeights := {r : ∀ i, Fin ((y i).val+1) // StrictMono (fun i => (r i).val)}
abbrev Survivor := {P : LayeredPathFamily (edges y) start finish //
  ¬(pathCollisionTimes P.path).Nonempty}

def strictHeightFamily (r : StrictHeights y) : Survivor y :=
  ⟨heightFamily y r.val, heightFamily_disjoint_of_strict y r.val r.property⟩

theorem heightFamily_injective : Function.Injective (heightFamily y) := by
  intro r q h
  funext i
  apply heightPath_injective y i
  apply LayeredPath.ext
  exact congrArg (fun P => P.path i) h

theorem strictHeightFamily_injective : Function.Injective (strictHeightFamily y) := by
  intro r q h
  apply Subtype.ext
  exact heightFamily_injective y (congrArg Subtype.val h)

def identityFamilyPath (P : LayeredPathFamily (edges y) start finish)
    (hp : P.matching = 1) (i : Fin d) : LayeredPath (edges y) (start i) (finish i) where
  vertex := P.path i
  start := P.start i
  finish := by simpa only [hp, Equiv.Perm.one_apply] using P.finish i
  edges := P.edges i

theorem heightFamily_surjective_identity (P : LayeredPathFamily (edges y) start finish)
    (hp : P.matching = 1) : ∃ r, heightFamily y r = P := by
  let r := fun i => (heightPathEquiv y i).symm (identityFamilyPath y P hp i)
  refine ⟨r, ?_⟩
  apply LayeredPathFamily.ext
  · exact hp.symm
  · funext i
    exact congrArg LayeredPath.vertex ((heightPathEquiv y i).apply_symm_apply
      (identityFamilyPath y P hp i))

theorem strictHeightFamily_surjective (hy : Monotone (fun i => (y i).val)) :
    Function.Surjective (strictHeightFamily y) := by
  intro P
  have hm := nonintersecting_matching_identity y hy P.val P.property
  obtain ⟨r, hr⟩ := heightFamily_surjective_identity y P.val hm
  have hc : ¬(pathCollisionTimes (heightFamily y r).path).Nonempty := by
    rw [hr]
    exact P.property
  refine ⟨⟨r, heightFamily_strict_of_disjoint y hy r hc⟩, ?_⟩
  exact Subtype.ext hr

def survivorEquiv (hy : Monotone (fun i => (y i).val)) : StrictHeights y ≃ Survivor y :=
  Equiv.ofBijective (strictHeightFamily y)
    ⟨strictHeightFamily_injective y, strictHeightFamily_surjective y hy⟩

theorem heightFamily_weight {R : Type*} [CommRing R] (slot : Fin (M+1) → R)
    (r : ∀ i, Fin ((y i).val+1)) :
    pathFamilyWeight (edgeWeight slot) (heightFamily y r) =
      ∏ i, slot ⟨(r i).val, by have h := (y i).isLt; have hr := (r i).isLt; omega⟩ := by
  change ((1 : Equiv.Perm (Fin d)).sign : ℤ) •
    (∏ k, ∏ i, edgeWeight slot k ((heightPath y i (r i)).vertex k.castSucc)
      ((heightPath y i (r i)).vertex k.succ)) = _
  simp only [map_one, Int.cast_one, Units.val_one, one_smul]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  exact heightPath_weight y i slot (r i)

theorem path_determinant_strict_heights {R : Type*} [CommRing R]
    (hy : Monotone (fun i => (y i).val)) (slot : Fin (M+1) → R) :
    Matrix.det (fun i j : Fin d =>
      ∑ P : LayeredPath (edges y) (start j) (finish i), layeredPathWeight (edgeWeight slot) P) =
      ∑ r : StrictHeights y, ∏ i, slot ⟨(r.val i).val, by
        have h := (y i).isLt; have hr := (r.val i).isLt; omega⟩ := by
  classical
  rw [determinant_eq_disjoint_sum]
  rw [← Equiv.sum_comp (survivorEquiv y hy) (fun P => pathFamilyWeight (edgeWeight slot) P.val)]
  apply Finset.sum_congr rfl
  intro r _
  exact heightFamily_weight y slot r.val

end
end Schubert.RS.HallLattice
