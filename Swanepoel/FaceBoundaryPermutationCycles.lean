module
public import Swanepoel.FaceBoundaryPermutation
public import Mathlib.Dynamics.PeriodicPts.Lemmas
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

structure FaceBoundaryCycle {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) (initial : OrientedEdge G) where
  length : ℕ
  length_pos : 0<length
  edge : Fin (length+1) → OrientedEdge G
  starts : edge 0=initial
  closes : edge (Fin.last length)=edge 0
  step : ∀ i : Fin length, G.faceBoundarySuccessor (edge i.castSucc)=edge i.succ
  face : ∀ i, G.sourceFace (edge i)=F
  edge_injective : Function.Injective (fun i : Fin length => edge i.castSucc)

theorem PennyGraph.minimal_face_boundary_cycle {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (initial : OrientedEdge G) (hF : G.sourceFace initial=F) :
    Nonempty (FaceBoundaryCycle G F initial) := by
  let S : OrientedEdge G → OrientedEdge G := G.faceBoundarySuccessor
  let L := Function.minimalPeriod S initial
  have hperiodic : initial∈Function.periodicPts S :=
    G.faceBoundarySuccessor.injective.mem_periodicPts initial
  have hL : 0<L := Function.minimalPeriod_pos_of_mem_periodicPts hperiodic
  have hface (k : ℕ) : G.sourceFace (S^[k] initial)=F := by
    induction k with
    | zero => exact hF
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (G.faceBoundarySuccessor_face (S^[k] initial)).trans ih
  refine ⟨{
    length := L
    length_pos := hL
    edge := fun i => S^[i.val] initial
    starts := rfl
    closes := ?_
    step := ?_
    face := fun i => hface i.val
    edge_injective := ?_ }⟩
  · change S^[L] initial=initial
    exact Function.isPeriodicPt_minimalPeriod S initial
  · intro i
    exact (Function.iterate_succ_apply' S i.val initial).symm
  · intro i j h
    apply Fin.ext
    exact Function.iterate_injOn_Iio_minimalPeriod (f := S) (x := initial) i.isLt j.isLt h

theorem PennyGraph.faceBoundaryPredecessor_ne_reverse {n : ℕ} (G : PennyGraph n)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (e : OrientedEdge G) : G.faceBoundaryPredecessor e≠reverseEdge e := by
  intro heq
  let a : VertexRay G e.val.1 := ⟨e.val.2,e.property⟩
  have hval : (G.vertexRayRotation e.val.1 a).val=a.val :=
    congrArg (fun d : OrientedEdge G => d.val.1) heq
  have hrot : G.vertexRayRotation e.val.1 a=a := Subtype.ext hval
  obtain ⟨c,hc,hne⟩ := hdegree e.val.1 e.val.2 e.property
  have hgap := clockwiseRayPermutation_empty (G.vertexDirection e.val.1)
    (G.vertexDirection_norm e.val.1) (G.vertexDirection_injective e.val.1) a ⟨c,hc⟩
  change ¬ClockwiseRayBetween (G.vertexDirection e.val.1 a)
    (G.vertexDirection e.val.1 (G.vertexRayRotation e.val.1 a)) (G.vertexDirection e.val.1 ⟨c,hc⟩) at hgap
  rw [hrot] at hgap
  apply hgap
  have hdirNe : G.vertexDirection e.val.1 ⟨c,hc⟩≠G.vertexDirection e.val.1 a := by
    intro h
    exact hne (congrArg Subtype.val (G.vertexDirection_injective e.val.1 h))
  simpa [ClockwiseRayBetween] using hdirNe

theorem PennyGraph.faceBoundarySuccessor_ne_reverse {n : ℕ} (G : PennyGraph n)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (e : OrientedEdge G) : G.faceBoundarySuccessor e≠reverseEdge e := by
  intro heq
  apply G.faceBoundaryPredecessor_ne_reverse hdegree (G.faceBoundarySuccessor e)
  have hinverse : G.faceBoundaryPredecessor (G.faceBoundarySuccessor e)=e :=
    G.faceBoundaryPredecessor.apply_symm_apply e
  rw [hinverse,heq,reverseEdge_involutive]

namespace FaceBoundaryCycle
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} {initial : OrientedEdge G}
    (C : FaceBoundaryCycle G F initial)

def vertex (i : Fin (C.length+1)) : Fin n := (C.edge i).val.1

theorem vertex_closes : C.vertex (Fin.last C.length)=C.vertex 0 :=
  congrArg (fun e : OrientedEdge G => e.val.1) C.closes

theorem edge_start (i : Fin C.length) : (C.edge i.castSucc).val.1=C.vertex i.castSucc := rfl

theorem edge_end (i : Fin C.length) : (C.edge i.castSucc).val.2=C.vertex i.succ := by
  have h := congrArg (fun e : OrientedEdge G => e.val.1) (C.step i)
  rw [G.faceBoundarySuccessor_start] at h
  exact h

theorem no_reverse (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (i : Fin C.length) : C.edge i.succ≠reverseEdge (C.edge i.castSucc) := by
  rw [← C.step i]
  exact G.faceBoundarySuccessor_ne_reverse hdegree _

theorem initial_occurs_once (i : Fin C.length) (heq : C.edge i.castSucc=initial) : i.val=0 := by
  let z : Fin C.length := ⟨0,C.length_pos⟩
  have hz : C.edge z.castSucc=initial := C.starts
  have hi : i=z := C.edge_injective (heq.trans hz.symm)
  exact congrArg Fin.val hi

theorem carried_sum : (∑ i : Fin C.length, carriedVector (C.edge i.castSucc))=0 := by
  have hcarried (i : Fin C.length) : carriedVector (C.edge i.castSucc)=
      G.point (C.vertex i.succ)-G.point (C.vertex i.castSucc) := by
    change G.point (C.edge i.castSucc).val.2-G.point (C.edge i.castSucc).val.1=_
    rw [C.edge_end i,C.edge_start i]
  simp_rw [hcarried]
  have h := polygon_edge_sum (fun k => G.point (C.vertex k))
  rw [C.vertex_closes,sub_self] at h
  exact h

theorem normal_sum : (∑ i : Fin C.length, sourceNormal (C.edge i.castSucc))=0 := by
  simp only [← rightNormalMap_carriedVector]
  rw [← map_sum,C.carried_sum,map_zero]

theorem port_membership (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht) (i : Fin C.length) :
    C.edge i.castSucc∈G.faceSourcePorts F := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_,C.face _⟩
  apply G.spineSource_of_sourceFace_mem_defects ht
  rw [C.face]
  exact hF

end FaceBoundaryCycle
end Swanepoel
