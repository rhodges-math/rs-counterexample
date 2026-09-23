import Schubert.RS.OperatorCyclicSpan
import Schubert.RS.Sl2FullPrimitive

namespace Schubert.RS.Representation
noncomputable section

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  {h e f : L} (t : IsSl2Triple h e f)
  {R X : Type*} [LieRing R] [LieAlgebra ℂ R]
  [LieRingModule (t.toLieSubalgebra ℂ) R] [LieModule ℂ (t.toLieSubalgebra ℂ) R]
  [AddCommGroup X] [Module ℂ X]
  [LieRingModule (t.toLieSubalgebra ℂ) X] [LieModule ℂ (t.toLieSubalgebra ℂ) X]
  [LieRingModule R X] [LieModule ℂ R X]
  [IsLieTower (t.toLieSubalgebra ℂ) R X]

def raisingRadicalOperators : Unit ⊕ R → Module.End ℂ X
  | .inl _ => LieModule.toEnd ℂ _ X (sl2RaisingElement t)
  | .inr r => LieModule.toEnd ℂ R X r

def raisingRadicalCyclicSpan (z : X) : Submodule ℂ X :=
  operatorCyclicSpan (raisingRadicalOperators t (R := R)) z

variable (z : X)

theorem raisingRadicalCyclicSpan_cartan (c : ℂ)
    (hz : ⁅sl2CartanElement t,z⁆=c • z) {x : X}
    (hx : x∈raisingRadicalCyclicSpan t (R := R) z) :
    ⁅sl2CartanElement t,x⁆∈raisingRadicalCyclicSpan t (R := R) z := by
  apply operatorCyclicSpan_extra (raisingRadicalOperators t (R := R)) z
    (LieModule.toEnd ℂ _ X (sl2CartanElement t)) _ _ hx
  · change ⁅sl2CartanElement t,z⁆∈_
    rw [hz]
    exact (raisingRadicalCyclicSpan t (R := R) z).smul_mem c
      (operatorCyclicSpan_generator _ z)
  · intro j y hy
    cases j with
    | inl u =>
      change ⁅sl2CartanElement t,⁅sl2RaisingElement t,y⁆⁆-
        ⁅sl2RaisingElement t,⁅sl2CartanElement t,y⁆⁆∈_
      rw [← lie_lie,(sl2SubalgebraTriple t).lie_h_e_smul (R := ℂ),smul_lie]
      exact (raisingRadicalCyclicSpan t (R := R) z).smul_mem 2
        (operatorCyclicSpan_stable (raisingRadicalOperators t (R := R) (X := X)) z (.inl ()) hy)
    | inr r =>
      change ⁅sl2CartanElement t,⁅r,y⁆⁆-⁅r,⁅sl2CartanElement t,y⁆⁆∈_
      rw [IsLieTower.leibniz_lie,add_sub_cancel_right]
      exact operatorCyclicSpan_stable _ z (.inr ⁅sl2CartanElement t,r⁆) hy

theorem raisingRadicalCyclicSpan_lowering (c : ℂ)
    (hh : ⁅sl2CartanElement t,z⁆=c • z) (hf : ⁅sl2LoweringElement t,z⁆=0)
    {x : X} (hx : x∈raisingRadicalCyclicSpan t (R := R) z) :
    ⁅sl2LoweringElement t,x⁆∈raisingRadicalCyclicSpan t (R := R) z := by
  apply operatorCyclicSpan_extra (raisingRadicalOperators t (R := R)) z
    (LieModule.toEnd ℂ _ X (sl2LoweringElement t)) _ _ hx
  · change ⁅sl2LoweringElement t,z⁆∈_
    rw [hf]
    exact (raisingRadicalCyclicSpan t (R := R) z).zero_mem
  · intro j y hy
    cases j with
    | inl u =>
      change ⁅sl2LoweringElement t,⁅sl2RaisingElement t,y⁆⁆-
        ⁅sl2RaisingElement t,⁅sl2LoweringElement t,y⁆⁆∈_
      rw [← lie_lie,← lie_skew (sl2LoweringElement t) (sl2RaisingElement t),
        (sl2SubalgebraTriple t).lie_e_f,neg_lie]
      exact (raisingRadicalCyclicSpan t (R := R) z).neg_mem
        (raisingRadicalCyclicSpan_cartan t z c hh hy)
    | inr r =>
      change ⁅sl2LoweringElement t,⁅r,y⁆⁆-⁅r,⁅sl2LoweringElement t,y⁆⁆∈_
      rw [IsLieTower.leibniz_lie,add_sub_cancel_right]
      exact operatorCyclicSpan_stable _ z (.inr ⁅sl2LoweringElement t,r⁆) hy

/-- The upper cyclic subspace of a lowest Cartan-weight vector is stable
under the full root algebra. -/
def raisingRadicalCyclicLieSubmodule (c : ℂ)
    (hh : ⁅sl2CartanElement t,z⁆=c • z) (hf : ⁅sl2LoweringElement t,z⁆=0) :
    LieSubmodule ℂ (t.toLieSubalgebra ℂ) X where
  toSubmodule := raisingRadicalCyclicSpan t (R := R) z
  lie_mem := by
    intro a x hx
    obtain ⟨u,v,w,rfl⟩ := sl2_element_expansion t a
    rw [add_lie,add_lie,smul_lie,smul_lie,smul_lie]
    apply (raisingRadicalCyclicSpan t (R := R) z).add_mem
    · apply (raisingRadicalCyclicSpan t (R := R) z).add_mem
      · exact (raisingRadicalCyclicSpan t (R := R) z).smul_mem u
          (operatorCyclicSpan_stable (raisingRadicalOperators t (R := R) (X := X)) z (.inl ()) hx)
      · exact (raisingRadicalCyclicSpan t (R := R) z).smul_mem v
          (raisingRadicalCyclicSpan_lowering t z c hh hf hx)
    · exact (raisingRadicalCyclicSpan t (R := R) z).smul_mem w
        (raisingRadicalCyclicSpan_cartan t z c hh hx)

end
end Schubert.RS.Representation
