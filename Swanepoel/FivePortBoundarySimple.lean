module
public import Swanepoel.FivePortBoundaryCycle
public import Mathlib.Tactic.FinCases
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace FaceBoundaryCycle
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} {initial : OrientedEdge G}
    (C : FaceBoundaryCycle G F initial)

theorem five_vertex_injective (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (hfive : C.length=5) : Function.Injective (fun i : Fin 5 => C.vertexAt i.val) := by
  have a01 := C.vertexAt_contact 0 (by omega)
  have a12 := C.vertexAt_contact 1 (by omega)
  have a23 := C.vertexAt_contact 2 (by omega)
  have a34 := C.vertexAt_contact 3 (by omega)
  have a40 : G.graph.Adj (C.vertexAt 4) (C.vertexAt 0) := by
    have h := C.vertexAt_contact 4 (by omega)
    have hclose : C.vertexAt 5=C.vertexAt 0 := by simpa only [hfive] using C.vertexAt_closes
    rwa [hclose] at h
  have h01 := a01.ne
  have h12 := a12.ne
  have h23 := a23.ne
  have h34 := a34.ne
  have h04 := a40.ne.symm
  have h02 := C.vertexAt_no_backtrack hdegree 0 (by omega)
  have h13 := C.vertexAt_no_backtrack hdegree 1 (by omega)
  have h24 := C.vertexAt_no_backtrack hdegree 2 (by omega)
  have h03 : C.vertexAt 0≠C.vertexAt 3 := by
    intro heq
    exact ht _ _ _ a01 a12 (by rw [heq]; exact a23)
  have h14 : C.vertexAt 1≠C.vertexAt 4 := by
    intro heq
    exact ht _ _ _ a12 a23 (by rw [heq]; exact a34)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | exact False.elim (h01 hij)
    | exact False.elim (h01 hij.symm)
    | exact False.elim (h02 hij)
    | exact False.elim (h02 hij.symm)
    | exact False.elim (h03 hij)
    | exact False.elim (h03 hij.symm)
    | exact False.elim (h04 hij)
    | exact False.elim (h04 hij.symm)
    | exact False.elim (h12 hij)
    | exact False.elim (h12 hij.symm)
    | exact False.elim (h13 hij)
    | exact False.elim (h13 hij.symm)
    | exact False.elim (h14 hij)
    | exact False.elim (h14 hij.symm)
    | exact False.elim (h23 hij)
    | exact False.elim (h23 hij.symm)
    | exact False.elim (h24 hij)
    | exact False.elim (h24 hij.symm)
    | exact False.elim (h34 hij)
    | exact False.elim (h34 hij.symm)

end FaceBoundaryCycle

theorem PennyGraph.five_port_defect_simple_cycle {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (hfive : (G.faceSourcePorts F).card=5) :
    ∃ initial : OrientedEdge G, ∃ C : FaceBoundaryCycle G F initial,
      C.length=5 ∧ C.dartSet=G.faceSourcePorts F ∧
        Function.Injective (fun i : Fin 5 => C.vertexAt i.val) := by
  obtain ⟨initial,C,hL,hports⟩ := G.five_port_defect_coherent_cycle ht F hF hdegree hfive
  exact ⟨initial,C,hL,hports,C.five_vertex_injective ht hdegree hL⟩

end Swanepoel
