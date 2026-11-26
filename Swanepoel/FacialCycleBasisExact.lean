module
public import Swanepoel.FacialCycleBasis
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def PennyGraph.contactCochainL2 {n : ℕ} (G : PennyGraph n)
    (weight : OrientedEdge G → ℝ) : EuclideanSpace ℝ (ContactEdge G) :=
  (WithLp.linearEquiv 2 ℝ (ContactEdge G → ℝ)).symm (fun e => weight e.forwardEdge)

@[simp] theorem PennyGraph.contactCochainL2_apply {n : ℕ} (G : PennyGraph n)
    (weight : OrientedEdge G → ℝ) (e : ContactEdge G) :
    G.contactCochainL2 weight e = weight e.forwardEdge := rfl

theorem PennyGraph.face_incidence_inner_cochain {n : ℕ} (G : PennyGraph n)
    (weight : OrientedEdge G → ℝ) (hreverse : ∀ e, weight (reverseEdge e) = -weight e)
    (F : BoundedFace G) :
    inner ℝ (G.boundedFaceIncidenceL2 F) (G.contactCochainL2 weight) =
      ∑ e ∈ G.faceIncidentDarts (G.boundedFaceAsPlane F), weight e := by
  rw [G.face_dart_curl_eq_incidence_sum (G.boundedFaceAsPlane F) weight hreverse]
  simp only [PiLp.inner_apply,RCLike.inner_apply,starRingEnd_apply,star_trivial,
    PennyGraph.boundedFaceIncidenceL2_apply,PennyGraph.contactCochainL2_apply,
    PennyGraph.boundedFaceIncidence,smul_eq_mul,mul_comm]

theorem PennyGraph.contactCochain_mem_gradient_range_of_face_curl_zero {n : ℕ}
    (G : PennyGraph n) (hc : G.graph.Connected)
    (weight : OrientedEdge G → ℝ) (hreverse : ∀ e, weight (reverseEdge e) = -weight e)
    (hcurl : ∀ F : BoundedFace G,
      (∑ e ∈ G.faceIncidentDarts (G.boundedFaceAsPlane F), weight e) = 0) :
    G.contactCochainL2 weight ∈ LinearMap.range G.contactGradientL2 := by
  let z := G.contactCochainL2 weight
  have hgen (F : BoundedFace G) : inner ℝ z (G.boundedFaceIncidenceL2 F) = 0 := by
    rw [real_inner_comm,G.face_incidence_inner_cochain weight hreverse F,hcurl F]
  have hspan : G.facialSpan ≤ LinearMap.ker (innerₗ (EuclideanSpace ℝ (ContactEdge G)) z) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨F,rfl⟩
    exact hgen F
  have hz : z ∈ G.contactCycleSpaceᗮ := by
    apply (Submodule.mem_orthogonal' _ _).mpr
    intro v hv
    exact hspan ((G.facialSpan_eq_cycleSpace hc).symm ▸ hv)
  change z ∈ (LinearMap.range G.contactGradientL2)ᗮᗮ at hz
  rwa [Submodule.orthogonal_orthogonal] at hz

theorem PennyGraph.exists_scalar_potential_of_face_curl_zero {n : ℕ} (G : PennyGraph n)
    (hc : G.graph.Connected) (weight : OrientedEdge G → ℝ)
    (hreverse : ∀ e, weight (reverseEdge e) = -weight e)
    (hcurl : ∀ F : BoundedFace G,
      (∑ e ∈ G.faceIncidentDarts (G.boundedFaceAsPlane F), weight e) = 0) :
    ∃ P : Fin n → ℝ, ∀ e : OrientedEdge G, P e.val.2-P e.val.1 = weight e := by
  obtain ⟨P,hP⟩ := G.contactCochain_mem_gradient_range_of_face_curl_zero hc weight hreverse hcurl
  have hphysical (e : ContactEdge G) : P e.val.2-P e.val.1 = weight e.forwardEdge :=
    congrArg (fun z : EuclideanSpace ℝ (ContactEdge G) => z e) hP
  refine ⟨P,?_⟩
  intro e
  obtain ⟨p,hp | hp⟩ := e.exists_contact_orientation
  · rw [hp]
    exact hphysical p
  · rw [hp,hreverse]
    change P p.val.1-P p.val.2 = -weight p.forwardEdge
    linarith [hphysical p]

end Swanepoel
