module

public import Formalism.LocalRingCardinality.DataCD
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BaseLatticeIsUnimodular

@[expose] public section

noncomputable section

namespace HcInf

open Formalism.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

section Lie

variable (P Q : ℕ)

instance : BorelSpace (lieU P Q) := ⟨rfl⟩

end Lie

end HcInf
