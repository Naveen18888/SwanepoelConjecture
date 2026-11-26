module
public import Swanepoel.ContactGradient
public import Swanepoel.ContactGradientOrientations
public import Swanepoel.PolygonSeparationProof
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def PennyGraph.boundedFaceIncidenceL2 {n : ℕ} (G : PennyGraph n)
    (F : BoundedFace G) : EuclideanSpace ℝ (ContactEdge G) :=
  (WithLp.linearEquiv 2 ℝ (ContactEdge G → ℝ)).symm (G.boundedFaceIncidence F)

@[simp] theorem PennyGraph.boundedFaceIncidenceL2_apply {n : ℕ} (G : PennyGraph n)
    (F : BoundedFace G) (e : ContactEdge G) :
    G.boundedFaceIncidenceL2 F e = G.boundedFaceIncidence F e := rfl

theorem PennyGraph.boundedFaceIncidenceL2_linearIndependent {n : ℕ} (G : PennyGraph n) :
    LinearIndependent ℝ G.boundedFaceIncidenceL2 := by
  exact G.boundedFaceIncidence_linearIndependent.map'
    (WithLp.linearEquiv 2 ℝ (ContactEdge G → ℝ)).symm.toLinearMap
    (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ (ContactEdge G → ℝ)).symm.injective)

theorem PennyGraph.face_incidence_gradient_sum {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (f : Fin n → ℝ) :
    (∑ e : ContactEdge G, G.faceIncidence F e * (f e.val.2-f e.val.1)) = 0 := by
  have hreverse (e : OrientedEdge G) :
      (f (reverseEdge e).val.2-f (reverseEdge e).val.1) = -(f e.val.2-f e.val.1) := by
    simp only [reverseEdge]
    abel
  have h := G.face_dart_curl_eq_incidence_sum F (fun e => f e.val.2-f e.val.1) hreverse
  rw [G.face_incident_vertex_difference_sum F f] at h
  simpa only [smul_eq_mul,ContactEdge.forwardEdge] using h.symm

theorem PennyGraph.boundedFaceIncidenceL2_inner_gradient {n : ℕ} (G : PennyGraph n)
    (F : BoundedFace G) (f : Fin n → ℝ) :
    inner ℝ (G.contactGradientL2 f) (G.boundedFaceIncidenceL2 F) = 0 := by
  simpa only [PiLp.inner_apply,RCLike.inner_apply,starRingEnd_apply,star_trivial,
    PennyGraph.contactGradientL2_apply,PennyGraph.boundedFaceIncidenceL2_apply,
    PennyGraph.boundedFaceIncidence] using
    G.face_incidence_gradient_sum (G.boundedFaceAsPlane F) f

theorem PennyGraph.boundedFaceIncidenceL2_mem_cycleSpace {n : ℕ} (G : PennyGraph n)
    (F : BoundedFace G) : G.boundedFaceIncidenceL2 F ∈ G.contactCycleSpace := by
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨f,rfl⟩
  exact G.boundedFaceIncidenceL2_inner_gradient F f

def PennyGraph.facialSpan {n : ℕ} (G : PennyGraph n) :
    Submodule ℝ (EuclideanSpace ℝ (ContactEdge G)) :=
  Submodule.span ℝ (Set.range G.boundedFaceIncidenceL2)

theorem PennyGraph.facialSpan_le_cycleSpace {n : ℕ} (G : PennyGraph n) :
    G.facialSpan ≤ G.contactCycleSpace := by
  apply Submodule.span_le.mpr
  rintro _ ⟨F,rfl⟩
  exact G.boundedFaceIncidenceL2_mem_cycleSpace F

theorem PennyGraph.contactCycleSpace_finrank {n : ℕ} (G : PennyGraph n)
    (hc : G.graph.Connected) :
    Module.finrank ℝ G.contactCycleSpace = Fintype.card (BoundedFace G) := by
  have hd := G.contactCycleSpace_finrank_add_vertices hc
  have he := G.faceEuler_of_connected hc
  change (n : ℤ)-G.edgeCount+Fintype.card (BoundedFace G)=1 at he
  omega

theorem PennyGraph.facialSpan_eq_cycleSpace {n : ℕ} (G : PennyGraph n)
    (hc : G.graph.Connected) : G.facialSpan = G.contactCycleSpace := by
  apply Submodule.eq_of_le_of_finrank_eq G.facialSpan_le_cycleSpace
  rw [G.contactCycleSpace_finrank hc]
  exact finrank_span_eq_card G.boundedFaceIncidenceL2_linearIndependent

def PennyGraph.facialCycleVector {n : ℕ} (G : PennyGraph n) (F : BoundedFace G) :
    G.contactCycleSpace :=
  ⟨G.boundedFaceIncidenceL2 F,G.boundedFaceIncidenceL2_mem_cycleSpace F⟩

theorem PennyGraph.facialCycleVector_linearIndependent {n : ℕ} (G : PennyGraph n) :
    LinearIndependent ℝ G.facialCycleVector := by
  exact LinearIndependent.of_comp G.contactCycleSpace.subtype
    G.boundedFaceIncidenceL2_linearIndependent

def PennyGraph.facialCycleBasis {n : ℕ} (G : PennyGraph n) (hc : G.graph.Connected) :
    Module.Basis (BoundedFace G) ℝ G.contactCycleSpace :=
  basisOfLinearIndependentOfCardEqFinrank' G.facialCycleVector
    G.facialCycleVector_linearIndependent (G.contactCycleSpace_finrank hc).symm

@[simp] theorem PennyGraph.facialCycleBasis_apply {n : ℕ} (G : PennyGraph n)
    (hc : G.graph.Connected) (F : BoundedFace G) :
    G.facialCycleBasis hc F = G.facialCycleVector F := by
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) F

end Swanepoel
