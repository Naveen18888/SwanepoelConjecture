module
public import Swanepoel.PentagonCrossingDegree
@[expose] public section

noncomputable section
namespace Swanepoel

namespace PentagonFaceBoundary
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} (P : PentagonFaceBoundary G F)

def SingleSectorCone (normal : Plane) (a : Fin 5) : Prop :=
  Real.sqrt 3/2 < inner ℝ (carriedVector (P.dart (a+4))) normal ∨
    inner ℝ (carriedVector (P.dart a)) normal< -Real.sqrt 3/2

def DoubleSectorCone (normal : Plane) (a : Fin 5) : Prop :=
  (Real.sqrt 3/2 < inner ℝ (carriedVector (P.dart (a+4))) normal ∧
    Real.sqrt 3/2 < inner ℝ (carriedVector (P.dart (a+3))) normal) ∨
  (inner ℝ (carriedVector (P.dart a)) normal< -Real.sqrt 3/2 ∧
    inner ℝ (carriedVector (P.dart (a+1))) normal< -Real.sqrt 3/2)

theorem SectorWalk.first_cone {normal : Plane} {a b : Fin 5} {k : ℕ}
    (h : P.SectorWalk normal a b k) (hk : 0<k) : P.SingleSectorCone normal a := by
  cases h with
  | nil => omega
  | @cons a b c k hab _ =>
    rcases hab with ⟨_,hneg⟩ | ⟨ha,hpos⟩
    · exact Or.inr hneg
    · have hb : b=a+4 := by
        calc
          b=(b+1)+4 := by fin_cases b <;> decide
          _=a+4 := by rw [← ha]
      exact Or.inl (by simpa only [hb] using hpos)

theorem SectorWalk.first_two_cones {normal : Plane} {a b : Fin 5} {k : ℕ}
    (h : P.SectorWalk normal a b k) (hk : 2≤k) : P.DoubleSectorCone normal a := by
  have hsqrt := Real.sqrt_nonneg (3:ℝ)
  cases h with
  | nil => omega
  | @cons a b c k hab htail =>
    cases htail with
    | nil => omega
    | @cons b c d k hbc _ =>
      rcases hab with ⟨hb,h0⟩ | ⟨ha,h0⟩
      · rcases hbc with ⟨_,h1⟩ | ⟨hc,h1⟩
        · exact Or.inr ⟨h0,by simpa only [hb] using h1⟩
        · have hac : a=c := add_right_cancel (hb.symm.trans hc)
          rw [← hac] at h1
          exact False.elim (by linarith only [h0,h1,hsqrt])
      · rcases hbc with ⟨_,h1⟩ | ⟨hb,h1⟩
        · exact False.elim (by linarith only [h0,h1,hsqrt])
        · have hba : b=a+4 := by
            calc
              b=(b+1)+4 := by fin_cases b <;> decide
              _=a+4 := by rw [← ha]
          have hca : c=a+3 := by
            calc
              c=((c+1)+1)+3 := by fin_cases c <;> decide
              _=a+3 := by rw [← hb,← ha]
          exact Or.inl ⟨by simpa only [hba] using h0,by simpa only [hca] using h1⟩

end PentagonFaceBoundary

namespace PentagonSpokeLoops
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} {P : PentagonFaceBoundary G F}
    (K : PentagonSpokeLoops G F P)

theorem source_crossing_cones (ht : G.TriangleFree)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (e : OrientedEdge G) (heF : G.sourceFace e∈G.defectPlaneFaces ht) (heRoot : G.sourceFace e≠F) :
    (0<G.familyCrossingDegree (G.familyTrackComponents {F}) (edgeComponent e) →
      P.SingleSectorCone (sourceNormal e) (K.faceSector (G.sourceFace e))) ∧
    (G.familyCrossingDegree (G.familyTrackComponents {F}) (edgeComponent e)=2 →
      P.DoubleSectorCone (sourceNormal e) (K.faceSector (G.sourceFace e))) := by
  have he := G.spineSource_of_sourceFace_mem_defects ht e heF
  obtain ⟨t,hreach,htop⟩ := exists_spine_end e
  obtain ⟨p⟩ := PositiveSpineChain.exists_of_reach hreach
  have hport (i : Fin 5) : P.dart i∈G.faceSourcePorts F := by
    rw [← P.darts]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hne (i : Fin 5) : edgeComponent e≠edgeComponent (P.dart i) :=
    G.boundary_face_other_defect_component_ne ht hY F hFY hports (P.dart i) e (hport i) heF heRoot
  have hcount := p.pentagon_crossing_degree_le_hitCount P ht he htop hY hFY hports hne
  have hwalk := p.sector_walk P K ht hY hFY hports hne
  have hsector : K.vertexSector e.val.1=K.faceSector (G.sourceFace e) :=
    congrArg K.codeSector (K.defect_source_vertexCode ht e heF heRoot)
  rw [hsector] at hwalk
  constructor
  · intro hpositive
    exact hwalk.first_cone P (by omega)
  · intro htwo
    exact hwalk.first_two_cones P (by omega)

theorem source_crossing_data (ht : G.TriangleFree)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (e : OrientedEdge G) (heF : G.sourceFace e∈G.defectPlaneFaces ht) (heRoot : G.sourceFace e≠F) :
    G.familyCrossingDegree (G.familyTrackComponents {F}) (edgeComponent e)≤2 ∧
    (0<G.familyCrossingDegree (G.familyTrackComponents {F}) (edgeComponent e) →
      P.SingleSectorCone (sourceNormal e) (K.faceSector (G.sourceFace e))) ∧
    (G.familyCrossingDegree (G.familyTrackComponents {F}) (edgeComponent e)=2 →
      P.DoubleSectorCone (sourceNormal e) (K.faceSector (G.sourceFace e))) :=
  ⟨G.isolated_pentagon_crossing_degree_le_two ht hY F P hFY hports e heF heRoot,
    K.source_crossing_cones ht hY hFY hports e heF heRoot⟩

end PentagonSpokeLoops
end Swanepoel
