import RSCounterexample.GLRep.Borel.LocalCoefficients

/-!
# Semi-invariants and induced representations

Let a group `H` act on a space `W` by a representation `r`, and let `χ : H →* Kˣ` be a character.
The **`χ`-semi-invariants** of `r` are the vectors `w` with `r h w = χ(h)⁻¹ • w` for all `h`
(`GLRep.semiInvariants`). If a representation `ρ` of another monoid `G` on `W` commutes with
`r`, the semi-invariants form a subrepresentation of `ρ` (`GLRep.semiInvariantSubrep`).

The basic example is the **induced representation** `ind_H^G χ` [Jantzen, *Representations of
Algebraic Groups*, I.3.3]: for a subgroup `H` of a group `G`, the functions `f : G → K` with
`f(x h) = χ(h)⁻¹ f(x)`, on which `G` acts by left translation `(g · f)(x) = f(g⁻¹ x)`
(`GLRep.leftTranslation`, `GLRep.indRep`). Here `r` is right translation
`(h · f)(x) = f(x h)` (`GLRep.rightTranslation`). For `G = GL_n(K)`, `H = B` and `χ = η`, these
are the conventions of the flag-variety library for the sections of `𝓛(η)`; the coordinate-ring
version is `RSCounterexample.GLRep.Borel.Regular`.

**Frobenius reciprocity** `Hom_G(V, ind χ) ≃ Hom_H(V, K_χ)` (`GLRep.indFrobeniusEquiv`) is given
by evaluation at `1` in one direction and by `φ ↦ (v ↦ (x ↦ φ(x⁻¹ · v)))` in the other.
-/

namespace GLRep

open Module

noncomputable section

/-! ### Semi-invariants of commuting actions -/

section SemiInvariants

variable {K G H : Type*} [Field K] [Monoid G] [Group H]
variable {W : Type*} [AddCommGroup W] [Module K W]

/-- The **`χ`-semi-invariants** of a representation `r` of `H`: the vectors `w` with
`r h w = χ(h)⁻¹ • w` for all `h ∈ H`. -/
def semiInvariants (r : Representation K H W) (χ : H →* Kˣ) : Submodule K W where
  carrier := {w | ∀ h, r h w = (((χ h)⁻¹ : Kˣ) : K) • w}
  add_mem' {v w} hv hw h := by
    simp only [Set.mem_ofPred_eq] at hv hw ⊢
    rw [map_add, hv h, hw h, smul_add]
  zero_mem' h := by simp
  smul_mem' c w hw h := by
    simp only [Set.mem_ofPred_eq] at hw ⊢
    rw [map_smul, hw h, smul_comm]

theorem mem_semiInvariants {r : Representation K H W} {χ : H →* Kˣ} {w : W} :
    w ∈ semiInvariants r χ ↔ ∀ h, r h w = (((χ h)⁻¹ : Kˣ) : K) • w :=
  Iff.rfl

/-- If `ρ` commutes with `r`, the `χ`-semi-invariants of `r` form a subrepresentation of `ρ`. -/
def semiInvariantSubrep (ρ : Representation K G W) (r : Representation K H W)
    (hcomm : ∀ g h, ρ g ∘ₗ r h = r h ∘ₗ ρ g) (χ : H →* Kˣ) : Subrepresentation ρ :=
  ⟨semiInvariants r χ, fun g w hw h => by
    rw [← LinearMap.comp_apply, ← hcomm, LinearMap.comp_apply, hw h, map_smul]⟩

@[simp]
theorem toSubmodule_semiInvariantSubrep (ρ : Representation K G W) (r : Representation K H W)
    (hcomm : ∀ g h, ρ g ∘ₗ r h = r h ∘ₗ ρ g) (χ : H →* Kˣ) :
    (semiInvariantSubrep ρ r hcomm χ).toSubmodule = semiInvariants r χ :=
  rfl

end SemiInvariants

/-! ### Translations of functions on a group -/

section Translation

variable (K G : Type*) [Field K] [Group G]

/-- **Left translation** of `G` on the functions `G → K`: `(g · f)(x) = f(g⁻¹ x)`. -/
def leftTranslation : Representation K G (G → K) where
  toFun g := LinearMap.funLeft K K fun x => g⁻¹ * x
  map_one' := by
    ext f x
    simp [LinearMap.funLeft]
  map_mul' g g' := by
    ext f x
    simp [LinearMap.funLeft, mul_assoc]

/-- **Right translation** of `G` on the functions `G → K`: `(g · f)(x) = f(x g)`. -/
def rightTranslation : Representation K G (G → K) where
  toFun g := LinearMap.funLeft K K fun x => x * g
  map_one' := by
    ext f x
    simp [LinearMap.funLeft]
  map_mul' g g' := by
    ext f x
    simp [LinearMap.funLeft, mul_assoc]

variable {K G}

@[simp]
theorem leftTranslation_apply (g : G) (f : G → K) (x : G) :
    leftTranslation K G g f x = f (g⁻¹ * x) :=
  rfl

@[simp]
theorem rightTranslation_apply (g : G) (f : G → K) (x : G) :
    rightTranslation K G g f x = f (x * g) :=
  rfl

/-- Left and right translations commute. -/
theorem leftTranslation_comp_rightTranslation (g g' : G) :
    leftTranslation K G g ∘ₗ rightTranslation K G g' =
      rightTranslation K G g' ∘ₗ leftTranslation K G g := by
  ext f x
  simp [mul_assoc]

end Translation

/-! ### Induced representations -/

section Induced

variable {K G : Type*} [Field K] [Group G] (H : Subgroup G) (χ : H →* Kˣ)

/-- The space `ind_H^G χ` of functions `f : G → K` with `f(x h) = χ(h)⁻¹ f(x)`, as a
subrepresentation of the left translation representation. -/
def indSubrep : Subrepresentation (leftTranslation K G) :=
  semiInvariantSubrep (leftTranslation K G) ((rightTranslation K G).comp H.subtype)
    (fun g h => leftTranslation_comp_rightTranslation g h) χ

theorem mem_indSubrep {f : G → K} :
    f ∈ (indSubrep H χ).toSubmodule ↔ ∀ x (h : H), f (x * h) = (((χ h)⁻¹ : Kˣ) : K) * f x := by
  refine ⟨fun hf x h => congrFun (hf h) x, fun hf h => funext fun x => hf x h⟩

/-- The **induced representation** `ind_H^G χ`: the group `G` acts by left translation on the
functions `f : G → K` with `f(x h) = χ(h)⁻¹ f(x)`. -/
abbrev indRep : Representation K G (indSubrep H χ).toSubmodule :=
  (indSubrep H χ).toRepresentation

/-- The one-dimensional representation `K_χ` of `H`. -/
def characterRep : Representation K H K :=
  scaledRep (Representation.trivial K H K) χ

@[simp]
theorem characterRep_apply (h : H) (c : K) : characterRep H χ h c = (χ h : K) * c := by
  rw [characterRep, scaledRep_apply, Representation.trivial_apply, smul_eq_mul]

/-- **Evaluation at `1`**, `ind_H^G χ → K_χ`, an intertwining map of representations of `H`. -/
def indEvalOne :
    Representation.IntertwiningMap ((indRep H χ).comp H.subtype) (characterRep H χ) where
  toFun f := (f : G → K) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' h := by
    ext f
    change (f : G → K) ((h : G)⁻¹ * 1) = (χ h : K) * (f : G → K) 1
    have := (mem_indSubrep H χ).mp f.2 1 h⁻¹
    rw [one_mul, map_inv, inv_inv] at this
    rw [mul_one, ← this, Subgroup.coe_inv]

variable {H χ}
variable {V : Type*} [AddCommGroup V] [Module K V] {ρ : Representation K G V}

/-- The function `x ↦ φ(x⁻¹ · v)` attached to `v` by an `H`-map `φ : V → K_χ`. -/
def frobeniusMap (φ : Representation.IntertwiningMap (ρ.comp H.subtype) (characterRep H χ))
    (v : V) :
    (indSubrep H χ).toSubmodule :=
  ⟨fun x => φ (ρ x⁻¹ v), (mem_indSubrep H χ).mpr fun x h => by
    have hφ := (φ.isIntertwining _ _ h⁻¹ (ρ x⁻¹ v)).trans (characterRep_apply H χ h⁻¹ _)
    calc φ (ρ (x * h)⁻¹ v) = φ (ρ ((h⁻¹ : H) : G) (ρ x⁻¹ v)) := by
          rw [mul_inv_rev, map_mul, Module.End.mul_apply, Subgroup.coe_inv]
      _ = (χ h⁻¹ : K) * φ (ρ x⁻¹ v) := hφ
      _ = _ := by rw [map_inv]⟩

/-- **Frobenius reciprocity**: `Hom_G(V, ind_H^G χ) ≃ Hom_H(V, K_χ)`, by evaluation at `1`. -/
def indFrobeniusEquiv :
    ρ.IntertwiningMap (indRep H χ) ≃ₗ[K]
      Representation.IntertwiningMap (ρ.comp H.subtype) (characterRep H χ) where
  toFun Φ := (indEvalOne H χ).comp ⟨Φ.toLinearMap, fun h => Φ.isIntertwining' (h : G)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun φ := ⟨⟨⟨frobeniusMap φ, fun v w => Subtype.ext <| funext fun x => by
      simp [frobeniusMap]⟩, fun c v => Subtype.ext <| funext fun x => by
      simp [frobeniusMap]⟩, fun g => LinearMap.ext fun v => Subtype.ext <| funext fun x => by
      change φ (ρ x⁻¹ (ρ g v)) = φ (ρ (g⁻¹ * x)⁻¹ v)
      rw [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]⟩
  left_inv Φ := by
    ext v x
    change (Φ (ρ x⁻¹ v) : G → K) 1 = (Φ v : G → K) x
    rw [Φ.isIntertwining]
    change (Φ v : G → K) (x⁻¹⁻¹ * 1) = (Φ v : G → K) x
    rw [inv_inv, mul_one]
  right_inv φ := by
    ext v
    change φ (ρ 1⁻¹ v) = φ v
    simp

end Induced

end

end GLRep
