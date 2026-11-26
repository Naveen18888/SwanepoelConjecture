module
public import Swanepoel.FaceCycleArea
public import Swanepoel.FivePortBoundarySimple
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

structure PentagonFaceBoundary {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) where
  vertex : Fin 5→Fin n
  vertex_injective : Function.Injective vertex
  contact : ∀ i : Fin 5,G.graph.Adj (vertex i) (vertex (i+1))
  face : ∀ i : Fin 5,G.sourceFace ⟨(vertex i,vertex (i+1)),contact i⟩=F
  darts : Finset.univ.image (fun i : Fin 5 =>
    (⟨(vertex i,vertex (i+1)),contact i⟩ : OrientedEdge G))=G.faceSourcePorts F

namespace PentagonFaceBoundary
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} (P : PentagonFaceBoundary G F)

theorem diagonal_dist_gt_one (ht : G.TriangleFree) (i : Fin 5) :
    1<dist (G.point (P.vertex i)) (G.point (P.vertex (i+2))) := by
  have hne : i≠i+2 := by fin_cases i <;> decide
  have hv : P.vertex i≠P.vertex (i+2) := fun h => hne (P.vertex_injective h)
  apply G.two_step_dist_gt_one ht _ (P.vertex (i+1)) _ hv (P.contact i)
  simpa only [add_assoc,show (1:Fin 5)+1=2 by decide] using P.contact (i+1)

theorem third_vertex_dist_gt_one (ht : G.TriangleFree) (i : Fin 5) :
    1<dist (G.point (P.vertex i)) (G.point (P.vertex (i+3))) := by
  have h := P.diagonal_dist_gt_one ht (i+3)
  have heq : (i+3)+2=i := by fin_cases i <;> decide
  simpa only [heq,dist_comm] using h

end PentagonFaceBoundary

theorem unit_side_view_inner_gt_half (x y : Plane) (hx : 1≤‖x‖) (hy : 1≤‖y‖)
    (hstrict : 1<‖x‖ ∨ 1<‖y‖) (hside : ‖x-y‖=1) :
    ‖x‖*‖y‖/2 < inner ℝ x y := by
  have hprod : 1<‖x‖*‖y‖ := by
    rcases hstrict with h | h
    · have hm := mul_le_mul_of_nonneg_left hy (norm_nonneg x)
      nlinarith
    · have hm := mul_le_mul_of_nonneg_right hx (norm_nonneg y)
      nlinarith
  have h := norm_sub_sq_real x y
  rw [hside] at h
  nlinarith [sq_nonneg (‖x‖-‖y‖)]

theorem PentagonFaceBoundary.opposite_side_view_inner {n : ℕ} {G : PennyGraph n}
    {F : PlaneFace G} (P : PentagonFaceBoundary G F) (ht : G.TriangleFree)
    (i j : Fin 5) (hj : j=1 ∨ j=2 ∨ j=3) :
    let x := G.point (P.vertex (i+j))-G.point (P.vertex i)
    let y := G.point (P.vertex (i+j+1))-G.point (P.vertex i)
    ‖x‖*‖y‖/2 < inner ℝ x y := by
  let x := G.point (P.vertex (i+j))-G.point (P.vertex i)
  let y := G.point (P.vertex (i+j+1))-G.point (P.vertex i)
  have hxi : i+j≠i := by
    rcases hj with rfl | rfl | rfl <;> fin_cases i <;> decide
  have hyi : i+j+1≠i := by
    rcases hj with rfl | rfl | rfl <;> fin_cases i <;> decide
  have hx : 1≤‖x‖ := by
    change 1≤‖G.point (P.vertex (i+j))-G.point (P.vertex i)‖
    rw [← dist_eq_norm]
    exact G.separated _ _ (fun h => hxi (P.vertex_injective h))
  have hy : 1≤‖y‖ := by
    change 1≤‖G.point (P.vertex (i+j+1))-G.point (P.vertex i)‖
    rw [← dist_eq_norm]
    exact G.separated _ _ (fun h => hyi (P.vertex_injective h))
  have hstrict : 1<‖x‖ ∨ 1<‖y‖ := by
    rcases hj with rfl | rfl | rfl
    · right
      have heq : (i+1)+1=i+2 := by simp only [add_assoc]; rfl
      simpa only [y,heq,← dist_eq_norm,dist_comm] using P.diagonal_dist_gt_one ht i
    · left
      simpa only [x,← dist_eq_norm,dist_comm] using P.diagonal_dist_gt_one ht i
    · left
      simpa only [x,← dist_eq_norm,dist_comm] using P.third_vertex_dist_gt_one ht i
  have hside : ‖x-y‖=1 := by
    have heq : x-y=G.point (P.vertex (i+j))-G.point (P.vertex (i+j+1)) := by
      dsimp [x,y]
      abel
    rw [heq,← dist_eq_norm]
    exact (P.contact (i+j)).2
  exact unit_side_view_inner_gt_half x y hx hy hstrict hside

theorem PennyGraph.five_port_face_boundary {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (hfive : (G.faceSourcePorts F).card=5) : Nonempty (PentagonFaceBoundary G F) := by
  obtain ⟨e,C,hlen,hdarts,hinj⟩ := G.five_port_defect_simple_cycle ht F hF hdegree hfive
  let p : Fin 5→Fin n := fun i => C.vertexAt i.val
  have hclose : C.vertexAt 5=C.vertexAt 0 := by simpa only [hlen] using C.vertexAt_closes
  have hc (i : Fin 5) : G.graph.Adj (p i) (p (i+1)) := by
    have h := C.vertexAt_contact i.val (by have := i.isLt; omega)
    fin_cases i <;> simpa [p,hclose] using h
  have heq (i : Fin 5) : (⟨(p i,p (i+1)),hc i⟩ : OrientedEdge G)=
      C.edge (⟨i.val,by have := i.isLt; omega⟩ : Fin C.length).castSucc := by
    apply Subtype.ext
    rw [C.vertexAt_edge]
    fin_cases i <;> simp [p,hclose]
  refine ⟨⟨p,hinj,hc,?_,?_⟩⟩
  · intro i
    rw [heq]
    exact C.face _
  · rw [← hdarts]
    ext f
    simp only [FaceBoundaryCycle.dartSet,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨⟨i.val,by have := i.isLt; omega⟩, (heq i).symm⟩
    · rintro ⟨i,rfl⟩
      refine ⟨⟨i.val,by have := i.isLt; omega⟩,?_⟩
      exact heq _

end Swanepoel
