module
public import Swanepoel.FaceSignedArea
public import Swanepoel.FivePortBoundaryCycle
public import Swanepoel.PolygonIsoperimetryList
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def vertexStepList {k : ℕ} (p : Fin (k+1)→Plane) : List Plane :=
  List.ofFn (fun i : Fin k => p i.succ-p i.castSucc)

theorem vertexStepList_sum {k : ℕ} (p : Fin (k+1)→Plane) :
    (vertexStepList p).sum=p (Fin.last k)-p 0 := by
  rw [vertexStepList,List.sum_ofFn]
  exact polygon_edge_sum p

theorem vertexStepList_doubleArea {k : ℕ} (p : Fin (k+1)→Plane) :
    stepDoubleArea (p 0) (vertexStepList p)=∑ i : Fin k,cross2 (p i.castSucc) (p i.succ) := by
  induction k with
  | zero => simp [vertexStepList,stepDoubleArea]
  | succ k ih =>
    have hh := ih (fun i => p i.succ)
    simp only [vertexStepList,List.ofFn_succ,stepDoubleArea,Fin.sum_univ_succ,
      Fin.castSucc_zero,Fin.succ_zero_eq_one,add_sub_cancel] at hh ⊢
    simpa only [Fin.succ_castSucc] using congrArg (fun r => cross2 (p 0) (p 1)+r) hh

theorem vertexStepList_length {k : ℕ} (p : Fin (k+1)→Plane) :
    stepLength (vertexStepList p)=∑ i : Fin k,‖p i.succ-p i.castSucc‖ := by
  simp [stepLength,vertexStepList,List.map_ofFn,List.sum_ofFn]

namespace FaceBoundaryCycle
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} {initial : OrientedEdge G}
    (C : FaceBoundaryCycle G F initial)

theorem dartSet_mem_initial : initial∈C.dartSet := by
  refine Finset.mem_image.mpr ⟨⟨0,C.length_pos⟩,Finset.mem_univ _,?_⟩
  exact C.starts

theorem dartSet_successor_closed {e : OrientedEdge G} (he : e∈C.dartSet) :
    G.faceBoundarySuccessor e∈C.dartSet := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  rw [C.step]
  by_cases hi : i.val+1<C.length
  · refine Finset.mem_image.mpr ⟨⟨i.val+1,hi⟩,Finset.mem_univ _,?_⟩
    congr 1
  · have hlast : i.succ=Fin.last C.length := Fin.ext (by have := i.isLt; simp; omega)
    rw [hlast,C.closes,C.starts]
    exact C.dartSet_mem_initial

theorem dartSet_successor_iff (e : OrientedEdge G) :
    G.faceBoundarySuccessor e∈C.dartSet ↔ e∈C.dartSet := by
  have hsub : C.dartSet.image G.faceBoundarySuccessor⊆C.dartSet := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
    exact C.dartSet_successor_closed hg
  have heq : C.dartSet.image G.faceBoundarySuccessor=C.dartSet :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ G.faceBoundarySuccessor.injective])
  constructor
  · intro he
    rw [← heq] at he
    obtain ⟨g,hg,hge⟩ := Finset.mem_image.mp he
    exact (G.faceBoundarySuccessor.injective hge) ▸ hg
  · exact C.dartSet_successor_closed

theorem dartSet_subset_of_successor_closed (S : Finset (OrientedEdge G)) (hinit : initial∈S)
    (hS : ∀ e∈S,G.faceBoundarySuccessor e∈S) : C.dartSet⊆S := by
  have hall (i : Fin (C.length+1)) : C.edge i∈S := by
    induction i using Fin.induction with
    | zero => rw [C.starts]; exact hinit
    | succ i ih => rw [← C.step i]; exact hS _ ih
  intro e he
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  exact hall i.castSucc

theorem dartSet_area_bound (P : Fin n→Plane)
    (hunit : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=0 ∨ ‖P e.val.2-P e.val.1‖=1) :
    |(∑ e∈C.dartSet,cross2 (P e.val.1) (P e.val.2))/2|≤
      (∑ e∈C.dartSet,‖P e.val.2-P e.val.1‖)^2/(4*Real.pi) := by
  let p (i : Fin (C.length+1)) := P (C.vertex i)
  have hclosed : (vertexStepList p).sum=0 := by
    rw [vertexStepList_sum]
    change P (C.vertex (Fin.last C.length))-P (C.vertex 0)=0
    rw [C.vertex_closes,sub_self]
  have hsteps : ∀ d∈vertexStepList p,d=0 ∨ ‖d‖=1 := by
    intro d hd
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hd
    simpa only [p,← C.edge_start i,← C.edge_end i] using hunit (C.edge i.castSucc)
  have hh := closed_zero_or_unit_step_perimeter_bound (p 0) (vertexStepList p) hclosed hsteps
  rw [vertexStepList_doubleArea,vertexStepList_length] at hh
  simpa only [dartSet,Finset.sum_image (fun i _ j _ h => C.edge_injective h),
    C.edge_start,C.edge_end] using hh

end FaceBoundaryCycle
end Swanepoel
