import Schubert.RS.Representation.StringFiltrationStructure
import Schubert.RS.Representation.AdjacentSaturation
import Schubert.RS.SortingIndependence

namespace Schubert.RS.Representation
noncomputable section
set_option maxHeartbeats 20000
open FinPermutation Schubert

/-- The proved inclusion of the actual sorted-neighbor module. -/
def compositionAdjacentEmbedding {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left < u i.right) :
    compositionFlag (swapComposition u i) →ₗ[ℂ] compositionFlag u :=
  Submodule.inclusion (compositionFlag_adjacent_le u i hu)

def compositionRaising {n : ℕ} (u : Composition n) (i : AdjacentPosition n) :
    Module.End ℂ (compositionFlag u) where
  toFun p := ⟨matrixUnitDerivation i.left i.right p.val,
    upperCyclic_root_stable _ ⟨(i.left,i.right),i.left_lt_right⟩ p.property⟩
  map_add' p q := Subtype.ext ((matrixUnitDerivation i.left i.right).map_add p.val q.val)
  map_smul' c p := Subtype.ext ((matrixUnitDerivation i.left i.right).toLinearMap.map_smul c p.val)

def compositionLowering {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left < u i.right) : Module.End ℂ (compositionFlag u) where
  toFun p := ⟨matrixUnitDerivation i.right i.left p.val,
    adjacent_lowering_flagDemazure_stable _ _ i (by rwa [composition_extremalWeight]) p.property⟩
  map_add' p q := Subtype.ext ((matrixUnitDerivation i.right i.left).map_add p.val q.val)
  map_smul' c p := Subtype.ext ((matrixUnitDerivation i.right i.left).toLinearMap.map_smul c p.val)

theorem compositionAdjacentEmbedding_val {n : ℕ} (u : Composition n)
    (i : AdjacentPosition n) (hu : u i.left < u i.right)
    (p : compositionFlag (swapComposition u i)) :
    (compositionAdjacentEmbedding u i hu p).val = p.val :=
  Submodule.coe_inclusion (compositionFlag_adjacent_le u i hu) p

theorem compositionAdjacentEmbedding_equivariant {n : ℕ} (u : Composition n)
    (i : AdjacentPosition n) (hu : u i.left < u i.right) (t : DiagonalTorus n)
    (p : compositionFlag (swapComposition u i)) :
    compositionAdjacentEmbedding u i hu (compositionFlagTorus _ t p) =
      compositionFlagTorus u t (compositionAdjacentEmbedding u i hu p) := by
  apply Subtype.ext
  calc
    _ = (compositionFlagTorus (swapComposition u i) t p).val :=
      compositionAdjacentEmbedding_val u i hu _
    _ = polynomialTorus n t p.val := flagTorus_val _ _ _ _
    _ = polynomialTorus n t (compositionAdjacentEmbedding u i hu p).val :=
      congrArg (fun x => polynomialTorus n t x) (compositionAdjacentEmbedding_val u i hu p).symm
    _ = _ := (flagTorus_val _ _ _ _).symm

/-- The root-string filtration property for composition flag modules. -/
def CompositionStringFiltration {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left < u i.right) : Prop :=
  ∃ L, Nonempty (RankOneStringFiltration
    (compositionFlagTorus (swapComposition u i)) (compositionFlagTorus u) i L
    (compositionAdjacentEmbedding u i hu) (compositionRaising u i) (compositionLowering u i hu))

/-- This is the induction implication, not a proof of the filtration hypothesis.
Only the operator sorting recursion is imported from the root files. -/
theorem composition_character_ascent_of_string_filtration {n : ℕ}
    (u : Composition n) (i : AdjacentPosition n) (hu : u i.left < u i.right)
    (hF : CompositionStringFiltration u i hu)
    (hprev : HasTorusCharacter (compositionFlagTorus (swapComposition u i))
      (key (swapComposition u i))) :
    HasTorusCharacter (compositionFlagTorus u) (key u) := by
  obtain ⟨L, ⟨F⟩⟩ := hF
  rw [key_any_ascent u i hu]
  exact F.toStringSpectralFiltration.character_recursion_of_character hprev

end
end Schubert.RS.Representation




