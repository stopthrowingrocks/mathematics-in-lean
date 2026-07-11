The constructor <;> native_decide is negligable. When replacing it with sorry, the total time went up between runs. Also, I'm running into a problem with ssimp. If the total number of stars exceeds the RHS, rather than returning False it simply sets the RHS to zero and eliminates all the stars.

*Consider*: Make extract_stars also emit _elim statements for every adjacent cell if it does not already exist
