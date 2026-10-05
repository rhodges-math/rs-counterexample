import Schubert.FlagVarieties.Foundations.Schemes.FiniteSeparatedDetection
import Schubert.FlagVarieties.Foundations.Schemes.SelectedFlagGlobalFaithfulness
import Schubert.FlagVarieties.Foundations.Schemes.SelectedChartSeparated

/-!
# Separatedness of the original complete flag scheme

The original quotient Grassmannian projections jointly detect morphisms
from every scheme, without reducedness hypotheses. Their targets are
separated. Hence their product embeds the original flag scheme as a
monomorphism into a separated scheme, proving separatedness itself.
-/

noncomputable section
namespace FlagVarieties.Foundations.QuotientCharts
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

instance selectedFlagChartScheme_isSeparated :
    (selectedFlagChartScheme R n).IsSeparated :=
  separated_of_finite_jointly_mono
    (fun j : Fin (n+1) => selectedChartScheme R n (n-j.val))
    (selectedFlagChartSchemeStep R n)
    (fun _ F G h => selectedFlagMorphism_eq_of_projections_eq R F G h)

instance selectedFlagChartSchemeToSpec_isSeparated :
    IsSeparated (selectedFlagChartSchemeToSpec R n) := inferInstance

end FlagVarieties.Foundations.QuotientCharts
