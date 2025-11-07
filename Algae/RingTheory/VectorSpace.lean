import Algae.RingTheory.Module
import Algae.RingTheory.Field

class VectorSpace (F: Type u) (X: Type v) [Field F] [CommGroup X] extends Module F X
