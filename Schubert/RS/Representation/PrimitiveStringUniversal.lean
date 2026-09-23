import Schubert.RS.Representation.PrimitiveStringExtension

namespace Schubert.RS.Representation
noncomputable section
open LieModule Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]
  [Module.Finite ℂ M] {h e f : L} {m : M} {d : ℕ}
  {t : IsSl2Triple h e f} (P : t.HasPrimitiveVectorWith m (d:ℂ))
  {N : Type*} [AddCommGroup N] [Module ℂ N]
  [LieRingModule (t.toLieSubalgebra ℂ) N] [LieModule ℂ (t.toLieSubalgebra ℂ) N]

theorem primitiveStringHom_basis
    (Φ : primitiveStringModule P →ₗ⁅ℂ,t.toLieSubalgebra ℂ⁆ N) (k : Fin (d+1)) :
    Φ (primitiveStringBasis P k) = primitiveStringVector (sl2LoweringElement t)
      (Φ (primitiveStringBasis P 0)) k.val := by
  obtain ⟨k,hk⟩ := k
  induction k with
  | zero => simp
  | succ k ih =>
      have hkd : k < d := by omega
      have hkl : k < d+1 := by omega
      rw [← primitiveStringBasis_f P ⟨k,hkl⟩ hkd, Φ.map_lie, ih hkl,
        primitiveStringVector_succ]

theorem primitiveStringHom_ext
    {Φ Ψ : primitiveStringModule P →ₗ⁅ℂ,t.toLieSubalgebra ℂ⁆ N}
    (hΦ : Φ (primitiveStringBasis P 0) = Ψ (primitiveStringBasis P 0)) : Φ = Ψ := by
  have hh : Φ.toLinearMap = Ψ.toLinearMap := by
    apply (primitiveStringBasis P).ext
    intro k
    change Φ (primitiveStringBasis P k) = Ψ (primitiveStringBasis P k)
    rw [primitiveStringHom_basis P Φ k, primitiveStringHom_basis P Ψ k, hΦ]
  exact LieModuleHom.ext (LinearMap.congr_fun hh)

theorem primitiveStringLift_top [Module.Finite ℂ N] (z : N)
    (hz : ⁅sl2CartanElement t,z⁆ = (d:ℂ) • z) (he : ⁅sl2RaisingElement t,z⁆ = 0) :
    primitiveStringLift P z hz he (primitiveStringBasis P 0) = z := by
  change primitiveStringExtension P z (primitiveStringBasis P 0) = z
  rw [primitiveStringExtension_basis,Fin.val_zero,primitiveStringVector_zero]

/-- A finite highest-weight line has an actual universal integrable extension:
the lowering-string submodule already present in any finite ambient representation.
The target is any finite module for the generated sl₂ subalgebra. -/
theorem primitiveString_universal [Module.Finite ℂ N] (z : N)
    (hz : ⁅sl2CartanElement t,z⁆ = (d:ℂ) • z) (he : ⁅sl2RaisingElement t,z⁆ = 0) :
    ∃! Φ : primitiveStringModule P →ₗ⁅ℂ,t.toLieSubalgebra ℂ⁆ N,
      Φ (primitiveStringBasis P 0) = z := by
  refine ⟨primitiveStringLift P z hz he, primitiveStringLift_top P z hz he, ?_⟩
  intro Φ hΦ
  apply primitiveStringHom_ext P
  rw [hΦ,primitiveStringLift_top]

end
end Schubert.RS.Representation
