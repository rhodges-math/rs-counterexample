import Schubert.RS.ConcreteData

/-!
# The root pattern of the paper's rank-28 instance

These checks instantiate the class comparisons and source/target ordering in
the proof of the counterexample family. They do not assume an extraction rule.
-/

namespace Schubert.RS.Counterexample

/-- Classes 0 and 1 are the two sources; 2 through 8 are paired targets. -/
def coordinateClass : Fin 28 → Fin 9 :=
  ![0,0,0,0,1,1,1,1,2,3,4,5,6,7,8,0,0,0,1,1,1,8,7,6,5,4,3,2]

def sourceA : Fin 7 → Fin 28 := ![0,1,2,3,15,16,17]
def sourceB : Fin 7 → Fin 28 := ![4,5,6,7,18,19,20]
def target : Fin 14 → Fin 28 := ![8,9,10,11,12,13,14,21,22,23,24,25,26,27]

def isSource (i : Fin 28) : Prop := (coordinateClass i).val < 2
instance (i : Fin 28) : Decidable (isSource i) := inferInstanceAs (Decidable (_ < _))

def comparisonWeight (i j : Fin 28) : ℤ :=
  (if a i < a j then 1 else 0) + (if b i < b j then 1 else 0) +
    (if g i < g j then 1 else 0) - 1

theorem class_pattern : ∀ i j : Fin 28, i < j →
    comparisonWeight i j =
      if coordinateClass i = coordinateClass j then -1
      else if isSource i ∧ ¬isSource j then 1 else 0 := by decide

theorem residual_pattern : ∀ i : Fin 28,
    (c i : ℤ) - a i - b i = if isSource i then 1 else -1 := by decide

theorem sourceA_injective : Function.Injective sourceA := by decide
theorem sourceB_injective : Function.Injective sourceB := by decide
theorem target_injective : Function.Injective target := by decide

theorem sourceA_class : ∀ i, coordinateClass (sourceA i) = 0 := by decide
theorem sourceB_class : ∀ i, coordinateClass (sourceB i) = 1 := by decide
theorem target_not_source : ∀ i, ¬isSource (target i) := by decide

theorem coordinates_covered : ∀ i : Fin 28,
    (∃ j, sourceA j = i) ∨ (∃ j, sourceB j = i) ∨ (∃ j, target j = i) := by decide

/-- Each early target has four preceding positions from either source. -/
theorem sourceA_height : ∀ j : Fin 14,
    (Finset.univ.filter (fun i : Fin 7 => sourceA i < target j)).card =
      if j.val < 7 then 4 else 7 := by decide

theorem sourceB_height : ∀ j : Fin 14,
    (Finset.univ.filter (fun i : Fin 7 => sourceB i < target j)).card =
      if j.val < 7 then 4 else 7 := by decide

/-- The target matching reverses the order of the late half. -/
theorem target_pairing : ∀ i j : Fin 14,
    coordinateClass (target i) = coordinateClass (target j) ↔
      i = j ∨ i.val + j.val = 13 := by decide

end Schubert.RS.Counterexample
