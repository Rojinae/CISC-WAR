# CISC/CMPE 204 Modelling Project

Welcome to our project for CISC/CMPE 204!

Our project models the classic card game "War," analyzing its structure through logic and probability to simulate gameplay and explore theoretical outcomes. Our project aims to provide strategies and probabilities associated with each player’s moves, through key propositions (like who wins a round, whether a player's card is higher, and whether the deck is stacked) and constraints (such as Player A winning only when their card is higher). In War, two players each reveal the top card of their 26-card deck and the player with the higher card wins both cards. A "war" occurs if cards match, and extra cards are played until a winner is found.

To run our current model and see our solutions, the project should run out of `run.py`. Our model will build rules, and conditions for winning, and will also solve various example scenarios to provide insight into probabilities and outcomes

For more information on our game analysis, read our `modelling_report_draft.docx`.



## Members
* Rojina E
* Marcela Rojas 
* Sara Rodriguez-Bowen

## Structure

* `documents`: Contains folders with our draft and will have our final submissions. README.md files are included in both folders. The draft folder also contains the file `proofs.jp`.
* `test.py`:  The script will check for the right files and sufficient theory size.
* `run.py`: A wrapper script that includes all encodings for our key constraints and propositions
* `proofs.jp`: Includes broken-down gameplay scenarios in Jape notation. The proofs contain explanations beside formulae
* `Dockerfile`: File to universally check our code/how our code runs
