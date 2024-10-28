# CISC/CMPE 204 Modelling Project

Welcome to our project for CISC/CMPE 204!

Our project models the classic card game "War," analyzing its structure through logic and probability to simulate gameplay and explore theoretical outcomes. Our project aims to provide strategies and probabilities associated with each player’s moves, through key propositions (like who wins a round, whether a player's card is higher, and whether the deck is stacked) and constraints (such as Player A winning only when their card is higher). In War, two players each reveal the top card of their 26-card deck and the player with the higher card wins both cards. A "war" occurs if cards match, and extra cards are played until a winner is found.


## Members
* Rojina E
* Marcela Rojas 
* Sara Rodriguez-Bowen

## Structure

* `documents`: Contains folders with our draft and will have our final submissions. README.md files are included in both.
* `test.py`:  The script will check for the right files and sufficient theory size.
* `run.py`: A general wrapper script that includes all encodings for our key constraints and propositions
* `proofs.jp`: Include broken down gameplay scenario jape proofs with explanations
* `Dockerfile`: File to universally check our code/how our code runs


## Running With Docker

By far the most reliable way to get things running is with [Docker](https://www.docker.com). This section runs through the steps and extra tips to running with Docker. You can remove this section for your final submission, and replace it with a section on how to run your project.

1. First, download Docker https://www.docker.com/get-started

2. Navigate to your project folder on the command line.

3. We first have to build the course image. To do so use the command:
`docker build -t cisc204 .`

4. Now that we have the image we can run the image as a container by using the command: `docker run -it -v $(pwd):/PROJECT cisc204 /bin/bash`

    `$(pwd)` will be the current path to the folder and will link to the container

    `/PROJECT` is the folder in the container that will be tied to your local directory

5. From there the two folders should be connected, everything you do in one automatically updates in the other. For the project you will write the code in your local directory and then run it through the docker command line. A quick test to see if they're working is to create a file in the folder on your computer then use the terminal to see if it also shows up in the docker container.

### Mac Users w/ M1 Chips

If you happen to be building and running things on a Mac with an M1 chip, then you will likely need to add the following parameter to both the build and run scripts:

```
--platform linux/x86_64
```

For example, the build command would become:

```
docker build --platform linux/x86_64 -t cisc204 .
```

### Mount on Different OS'

In the run script above, the `-v $(pwd):/PROJECT` is used to mount the current directory to the container. If you are using a different OS, you may need to change this to the following:

- Windows PowerShell: `-v ${PWD}:/PROJECT`
- Windows CMD: `-v %cd%:/PROJECT`
- Mac: `-v $(pwd):/PROJECT`

Finally, if you are in a folder with a bunch of spaces in the absolute path, then it will break things unless you "quote" the current directory like this (e.g., on Windows CMD):

```
docker run -it -v "%cd%":/PROJECT cisc204
```
