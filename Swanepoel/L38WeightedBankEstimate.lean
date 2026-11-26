module
public import Swanepoel.L38BoundaryCalibration
public import Swanepoel.L38HalfAreaBankBoundary
public import Swanepoel.L38HalfPentagonFamilyCounts
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem half_weighted_bank_calibration (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool)
    (P : Fin (B.bankVertices side).card→Plane)
    (hP : ∀ e : OrientedEdge (B.halfGraph side),P e.val.2-P e.val.1=
      trackDisplacement ((B.halfGraph side).l38TrackWeight
        (B.halfRemainderDefects ht side) (B.halfIsolatedDefects ht side)) e) :
    4*l38CertificateArea*(∑ F : BoundedFace (B.halfGraph side),
      (B.halfGraph side).faceSignedArea P ((B.halfGraph side).boundedFaceAsPlane F))≤
      ((5/2:ℝ)*(B.isolatedTwoPortPentagons ht side).card+
        2*(G.familyK (B.bankRemainder ht side) : ℝ)-
        (G.familyPortExcess (B.bankRemainder ht side) : ℝ)-
        2*((B.isolatedTwoPortPentagons ht side).card+
          ((B.subfamilyMeetingPorts (B.bankRemainder ht side)).card : ℝ))/3)^2 := by
  let H := B.halfGraph side
  obtain ⟨outer,houter,_⟩ := H.exists_unique_outer_face
  have hdisp (e : OrientedEdge H) : P e.val.2-P e.val.1=
      B.halfWeightedLength ht side e • carriedVector e := by
    rw [hP]
    rfl
  have hcal := H.bounded_signed_area_bank_calibration P (B.halfBankAxis side) (B.halfBankAxis_norm side)
    (B.halfBankDart ht side) (B.halfWeightedLength ht side)
    (B.halfWeightedLength_nonneg ht side) hdisp outer houter
    (fun e _ he => (B.halfBankDart_normal_cone ht hc hcut side e he).le)
  have hnorm (e : OrientedEdge H) : ‖P e.val.2-P e.val.1‖=B.halfWeightedLength ht side e := by
    rw [hP,H.l38_displacement_norm]
    rfl
  have hperimeter := B.half_weighted_outer_perimeter_eq ht hc hcut side P hP outer houter
  simp_rw [hnorm] at hperimeter
  rw [l38BoundaryCost_sum,hperimeter,B.halfBankDart_sum ht hc hcut side outer houter] at hcal
  convert hcal using 1
  ring

theorem bank_weighted_area_estimate (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    let S := B.isolatedTwoPortPentagons ht side
    let Y := B.bankRemainder ht side
    ((G.familyInternalCrossings ht S : ℝ)+S.card)/4+
      (G.interFamilyCrossings ht S Y : ℝ)/2+((G.familyInternalCrossings ht Y : ℝ)+Y.card)≤
      (411/2500:ℝ)*((5/2:ℝ)*S.card+2*(G.familyK Y : ℝ)-(G.familyPortExcess Y : ℝ)-
        2*((S.card : ℝ)+(B.subfamilyMeetingPorts Y).card)/3)^2 := by
  dsimp only
  let H := B.halfGraph side
  let Y := B.halfRemainderDefects ht side
  let S := B.halfIsolatedDefects ht side
  let mass : ℝ := (H.familyInternalCrossings (B.halfGraph_triangleFree ht side) Y : ℝ)+Y.card+
    ((H.familyInternalCrossings (B.halfGraph_triangleFree ht side) S : ℝ)+S.card)/4+
      (H.interFamilyCrossings (B.halfGraph_triangleFree ht side) Y S : ℝ)/2
  let cost : ℝ := (5/2:ℝ)*(B.isolatedTwoPortPentagons ht side).card+
    2*(G.familyK (B.bankRemainder ht side) : ℝ)-(G.familyPortExcess (B.bankRemainder ht side) : ℝ)-
    2*(((B.isolatedTwoPortPentagons ht side).card : ℝ)+
      (B.subfamilyMeetingPorts (B.bankRemainder ht side)).card)/3
  obtain ⟨P,hP,hLower,_⟩ := B.exists_half_weighted_area_map ht hc hcut hdegree side
  change Real.sqrt 3/2*mass≤∑ F : BoundedFace H,H.faceSignedArea P (H.boundedFaceAsPlane F) at hLower
  have hCal := B.half_weighted_bank_calibration ht hc hcut side P hP
  change 4*l38CertificateArea*(∑ F : BoundedFace H,H.faceSignedArea P (H.boundedFaceAsPlane F))≤cost^2 at hCal
  have hmass : 0≤mass := by dsimp [mass]; positivity
  have hcoef := calibrated_area_coefficient mass _ cost l38CertificateArea hmass
    l38_certificate_area_threshold hLower hCal
  have hSSub : B.isolatedTwoPortPentagons ht side⊆B.bankDefectFamily ht side := Finset.filter_subset _ _
  have hYSub := B.bankRemainder_subset ht side
  change ((B.halfGraph side).familyInternalCrossings (B.halfGraph_triangleFree ht side)
      (B.bankDefectImage ht side (B.bankRemainder ht side) hYSub) : ℝ)+
    (B.bankDefectImage ht side (B.bankRemainder ht side) hYSub).card+
    (((B.halfGraph side).familyInternalCrossings (B.halfGraph_triangleFree ht side)
      (B.bankDefectImage ht side (B.isolatedTwoPortPentagons ht side) hSSub) : ℝ)+
      (B.bankDefectImage ht side (B.isolatedTwoPortPentagons ht side) hSSub).card)/4+
    ((B.halfGraph side).interFamilyCrossings (B.halfGraph_triangleFree ht side)
      (B.bankDefectImage ht side (B.bankRemainder ht side) hYSub)
      (B.bankDefectImage ht side (B.isolatedTwoPortPentagons ht side) hSSub) : ℝ)/2≤
      (411/2500:ℝ)*cost^2 at hcoef
  rw [B.bankDefectImage_internal_crossings ht side _ hYSub,
    B.bankDefectImage_internal_crossings ht side _ hSSub,
    B.bankDefectImage_inter_crossings ht side _ _ hYSub hSSub,
    B.bankDefectImage_card ht side _ hYSub,B.bankDefectImage_card ht side _ hSSub] at hcoef
  rw [G.l38_interFamilyCrossings_comm ht (B.bankRemainder ht side) (B.isolatedTwoPortPentagons ht side)] at hcoef
  dsimp only [cost] at hcoef
  linarith only [hcoef]

end OrdinaryCutBanks
end Swanepoel
