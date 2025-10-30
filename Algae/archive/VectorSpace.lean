import Algae.Module
import Algae.Field

class VectorSpace (F: Type u) (X: Type v) [Field F] [CommutativeGroup X] extends Module F X
