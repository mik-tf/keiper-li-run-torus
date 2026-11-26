import P3Lean.Core
import P3Lean.Data
import P3Lean.Weights
set_option maxRecDepth 100000
namespace P3Lean
theorem ok_kernel : checkChunk weightsRev rows = true := by decide +kernel
end P3Lean
#print axioms P3Lean.ok_kernel
