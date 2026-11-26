module
public import Swanepoel.PolygonSeparationAngles
@[expose] public section

noncomputable section
namespace Swanepoel

def PennyGraph.walkAngle {n : ℕ} (G : PennyGraph n) {S : Finset (ContactEdge G)}
    {a b : Fin n} (p : (G.contactGraph S).Walk a b) (z : Plane) : ℝ :=
  match p with
  | .nil => 0
  | .cons' a b _ _ p => segmentAngle (G.point a) (G.point b) z+G.walkAngle p z

theorem PennyGraph.walkAngle_coe {n : ℕ} (G : PennyGraph n) {S : Finset (ContactEdge G)}
    {a b : Fin n} (p : (G.contactGraph S).Walk a b) {z : Plane}
    (hz : z∉Set.range G.point) :
    (G.walkAngle p z : Real.Angle)=
      (Complex.arg (planeComplex (G.point b)-planeComplex z) : Real.Angle)-
        (Complex.arg (planeComplex (G.point a)-planeComplex z) : Real.Angle) := by
  have hne (i : Fin n) : G.point i≠z := fun h => hz ⟨i,h⟩
  induction p with
  | nil => simp [PennyGraph.walkAngle]
  | @cons a b c hab p ih =>
    rw [PennyGraph.walkAngle,Real.Angle.coe_add,segmentAngle_coe _ _ _ (hne a) (hne b),ih]
    abel

theorem PennyGraph.continuousAt_walkAngle {n : ℕ} (G : PennyGraph n)
    {S : Finset (ContactEdge G)} {a b : Fin n} (p : (G.contactGraph S).Walk a b)
    {z : Plane} (hz : z∉G.subdrawing S) : ContinuousAt (G.walkAngle p) z := by
  induction p with
  | nil => exact continuousAt_const
  | @cons a b c hab p ih =>
    change ContinuousAt (fun w => segmentAngle (G.point a) (G.point b) w+G.walkAngle p w) z
    apply (continuousAt_segmentAngle ?_).add ih
    intro hs
    apply hz
    apply G.contactGraph_edgeTrace_subset S hab
    rwa [G.edgeTrace_eq_segment]

def PennyGraph.closedPathAngle {n : ℕ} (G : PennyGraph n) {S : Finset (ContactEdge G)}
    {a b : Fin n} (p : (G.contactGraph S).Walk a b) (z : Plane) : ℝ :=
  G.walkAngle p z+segmentAngle (G.point b) (G.point a) z

theorem PennyGraph.closedPathAngle_mem_zmultiples {n : ℕ} (G : PennyGraph n)
    {S : Finset (ContactEdge G)} {a b : Fin n} (p : (G.contactGraph S).Walk a b)
    {z : Plane} (hz : z∉Set.range G.point) :
    G.closedPathAngle p z∈AddSubgroup.zmultiples (2*Real.pi) := by
  have hne (i : Fin n) : G.point i≠z := fun h => hz ⟨i,h⟩
  apply AddSubgroup.mem_zmultiples_iff.mpr
  apply Real.Angle.coe_eq_zero_iff.mp
  rw [PennyGraph.closedPathAngle,Real.Angle.coe_add,G.walkAngle_coe p hz,
    segmentAngle_coe _ _ _ (hne b) (hne a)]
  abel

theorem PennyGraph.continuousAt_closedPathAngle {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G)
    (p : (G.contactGraph S).Walk e.val.1 e.val.2) {z : Plane}
    (hz : z∉G.subdrawing (insert e S)) : ContinuousAt (G.closedPathAngle p) z := by
  have hS : z∉G.subdrawing S := fun h => hz ((G.subdrawing_mono (Finset.subset_insert _ _)) h)
  apply (G.continuousAt_walkAngle p hS).add (continuousAt_segmentAngle ?_)
  intro hs
  apply hz
  rw [G.subdrawing_insert]
  apply Or.inr
  rw [G.edgeTrace_reverse,G.edgeTrace_eq_segment]
  exact hs

theorem PennyGraph.closedPathAngle_constant_on_component {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G)
    (p : (G.contactGraph S).Walk e.val.1 e.val.2) {x y : Plane}
    (hx : x∉G.subdrawing (insert e S))
    (hy : y∈connectedComponentIn (G.subdrawing (insert e S))ᶜ x) :
    G.closedPathAngle p x=G.closedPathAngle p y := by
  have hdisc : IsDiscrete ((AddSubgroup.zmultiples (2*Real.pi) : AddSubgroup ℝ) : Set ℝ) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
  apply isPreconnected_connectedComponentIn.constant_of_mapsTo hdisc ?_ ?_
    (mem_connectedComponentIn hx) hy
  · intro z hz
    exact (G.continuousAt_closedPathAngle S e p (connectedComponentIn_subset _ _ hz)).continuousWithinAt
  · intro z hz
    apply G.closedPathAngle_mem_zmultiples p
    intro hr
    exact connectedComponentIn_subset _ _ hz (Or.inl hr)

end Swanepoel
