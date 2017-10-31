module Refined.Props.String

import Data.List
import Props.Util

%access public export

isEmpty : (s:String) -> Type 
isEmpty s = Dec ( (=) "" s)

NonEmpty : String -> Type
NonEmpty s = NotGiven (decEq "" s)
                 

