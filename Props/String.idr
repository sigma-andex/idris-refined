module Props.String

import Props.Util

%access public export

NonEmpty : String -> Type
NonEmpty s = Denied (decEq "" s)
