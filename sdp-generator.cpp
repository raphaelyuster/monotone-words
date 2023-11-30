#include <iostream>

/* constants corresponding to program parameters */
const int L = 7;				// word graphs on at most L vertices will be constructed
const int W = 6;				// alphabet size (change this tvalue to either 4,5,6 and run the program)
const int maxGraphs = 200000;	// an upper bound on the number of word graphs on L vertices
const int maxTypeOrder = 3;		// maximum order of a type being used
const int maxNumTypes = 9;		// number of types used
const int maxFlagsInList = 485; // an upper bound for the number of flags in a flag list
const int rawTypes[][1 + maxTypeOrder * (maxTypeOrder - 1) / 2] = {
	{1},						// the single vertex type
	{3,0,0,0},
	{3,0,0,1},
	{3,0,0,2},
	{3,0,1,1},
	{3,0,1,2},
	{3,1,1,1},
	{3,1,1,2},
	{3,2,2,2}
}; // the types in raw format. Each type is an array whose 0'th element is the order k of the type, followed by k(k-1)/2 numbers representing edge colors. E.g., {3, 1,0,2} rpresents a type of order 3 with c(0,1)=1 c(0,2)=0 c(1,2)=2

const int targetOrder = 3;	// max order of a target word graphs
const int numTargets = 9;	// the number of target word graphs
const int rawTargets[][targetOrder * (targetOrder - 1) / 2] = {
	{0,0,0},
	{1,1,1},
	{0,0,2},
	{0,2,0},
	{2,0,0},
	{2,2,2},
	{1,1,2},
	{1,2,1},
	{2,1,1}
}; // the targets, represented in raw format.

/* global variables */
int perm[L + 1][40320][L];									// perm[l] represents all permutations on {0,..,l-1}
int wordGraph[L + 1][maxGraphs][L][L];						// permGraphs[l] contains all non-isomorphic word graphs on l vertices
int wordGraphFingerprint[L + 1][maxGraphs];					// fingerprint speeding isomorphim check
int numWordGraphs[L + 1];									// numWordGraphs[l] is the numvber of non-isomprhic word graphs on l vertices
int numTypes;												// number of types
int typeSize[maxNumTypes];									// the size of each type
int type[maxNumTypes][maxTypeOrder][maxTypeOrder];			// adjacency matrix of each type
int flagList[maxNumTypes][maxFlagsInList][L + 1][L];		// last row are the indices of the type vertices -1 stands for unlabeled vertex
int flagListSize[maxNumTypes];								//  flagListSize[t] is the length of the flagList #t.
int SDarray[maxNumTypes][maxFlagsInList][maxFlagsInList];	// SDarray[i] is a square matrix indexed by the elements of a flag list
int target[numTargets][targetOrder][targetOrder];		    // adjacency matrix of each target word graph
int targetDensities[maxGraphs];								// target density of each graph

/* printing functions */

void printPermutation(int l, int p) { // l is the size of the permutation and p is the serial number of it
	for (int i = 0; i < l; i++)
		printf("%d", perm[l][p][i]);
	printf("\n");
}

void printGraph(int l, int g) { // l is the order and g is the serial number of the graph in the list of graphs of the given order
	printf("Graph #%d in list of graphs of order #%d:\n", g, l);
	for (int i = 0; i < l; i++) {
		for (int j = 0; j < l; j++)
			printf("%d ", wordGraph[l][g][i][j]);
		printf("\n");
	}
}

void printFlag(int s, int t) { // s is the flag list and t is the location of the flag in that list
	printf("Flag #%d in flag list #%d:\n", t, s);
	for (int i = 0; i < rawTypes[s][0] + (L - rawTypes[s][0] / 2); i++) {
		for (int j = 0; j < rawTypes[s][0] + (L - rawTypes[s][0] / 2); j++)
			printf("%d ", flagList[s][t][i][j]);
		printf("\n");
	}
	for (int i = 0; i < rawTypes[s][0] + (L - rawTypes[s][0] / 2); i++)
		if (flagList[s][t][L][i] != -1)
			printf("%d is labeled %d\n", i, flagList[s][t][L][i]);
}

void printWordGraphQuantities() {
	for (int i = 2; i <= L; i++)
		printf("Number of word graphs on %d vertices is %d\n", i, numWordGraphs[i]);
}

void printFlagListsQuantities() {
	for (int i = 0; i < numTypes; i++)
		printf("The size of flag list #%d is %d\n", i, flagListSize[i]);
}

void printFlagList(int s) {
	for (int t = 0; t < flagListSize[s]; t++)
		printFlag(s, t);
}

void printArray(int q, int g) {
	printf("Printing constraint array #%d for graph %d:\n", q, g);
	printGraph(L, g);
	int n = flagListSize[q];
	printf("Array dimensions is %d by %d.\n", n, n);
	int countNonNegative = 0;
	int countZeroRows = 0;
	int sum = 0;
	for (int i = 0; i < n; i++) {
		bool rowEmpty = true;
		for (int j = 0; j < n; j++) {
			if (SDarray[q][i][j] > 0) {
				countNonNegative++;
				rowEmpty = false;
				sum += SDarray[q][i][j];
			}
			printf("%2d ", SDarray[q][i][j]);
		}
		printf("\n");
		if (rowEmpty)
			countZeroRows++;
	}
	printf("The number of nonnegative entries is %d\n", countNonNegative);
	printf("The number of zero rows is %d\n", countZeroRows);
	printf("The sum of all entries is %d\n", sum);
}

void printTargetDensities() {
	int min = targetDensities[0];
	printf("Printing target densities for each graph\n");
	for (int i = 0; i < numWordGraphs[L]; i++) {
		printf("Graph #%d has density %d\n", i, targetDensities[i]);
		if (targetDensities[i] < min)
			min = targetDensities[i];
	}
	printf("Minimum density %d\n", min);
}

/* utility functions */

int fact(int n) {
	int f = 1;
	for (int i = 2; i <= n; i++)
		f *= i;
	return f;
}

/* operational functions */

void loadPermutations() {
	int fact = 1;
	for (int l = 1; l <= L; l++) {
		fact *= l;
		int n = l - 1;
		int t = 0;
		for (int j = 0; j < fact; j++)
			for (int k = l - 1; k >= 0; k--) {
				for (int q = 0; q < k; q++)
					perm[l][t][q] = perm[l - 1][j][q];
				perm[l][t][k] = n;
				for (int q = k + 1; q < l; q++)
					perm[l][t][q] = perm[l - 1][j][q - 1];
				t++;
			}
	}
}

void createGraph(int l, int w[]) { // create the word graph of the given word w of length l
	int count[3] = { 0,0,0 };
	for (int i = 0; i < l; i++)
		for (int j = i + 1; j < l; j++) {
			int v = 0;
			if (w[i] > w[j])
				v = 1;
			if (w[i] == w[j])
				v = 2;
			wordGraph[l][numWordGraphs[l]][i][j] = v;
			wordGraph[l][numWordGraphs[l]][j][i] = v;
			count[v]++;
		}
	wordGraphFingerprint[l][numWordGraphs[l]] = count[0] + 100 * count[1] + 10000 * count[2];
}


bool checkIsomorphic(int l, int i, int j) { // check if word graphs #i and  #j in the list of word graphs of order l are isomorphic
	if (wordGraphFingerprint[l][i] != wordGraphFingerprint[l][j])
		return false;
	int lfact = fact(l);
	for (int p = 0; p < lfact; p++) {
		bool good = true;
		for (int k = 0; k < l && good; k++)
			for (int m = 0; m < l && good; m++)
				if (k != m && wordGraph[l][i][perm[l][p][k]][perm[l][p][m]] != wordGraph[l][j][k][m])
					good = false;
		if (good)
			return true;
	}
	return false;
}

void constructGraphs() {
	int word[L];
	for (int l = 2; l <= L; l++) {
		numWordGraphs[l] = 0;
		for (int i = 0; i < l; i++)
			word[i] = 0;
		createGraph(l, word);
		numWordGraphs[l] = 1;
		while (1) {
			int i = 0;
			while (word[i] == W - 1 && i < l) {
				word[i] = 0;
				i++;
			}
			if (i == l)
				break;
			word[i]++;
			createGraph(l, word);
			int j;
			for (j = 0; j < numWordGraphs[l]; j++)
				if (checkIsomorphic(l, j, numWordGraphs[l]))
					break;
			if (j == numWordGraphs[l])
				numWordGraphs[l]++;
		}
	}
}

void loadTypes() {
	numTypes = sizeof(rawTypes) / sizeof(rawTypes[0]);
	for (int i = 0; i < numTypes; i++) {
		typeSize[i] = rawTypes[i][0];
		int t = 1;
		for (int j = 0; j < typeSize[i]; j++)
			for (int k = j + 1; k < typeSize[i]; k++) {
				int val = rawTypes[i][t++];
				type[i][j][k] = val;
				type[i][k][j] = val;
			}
	}
}

void loadTargets() {
	for (int i = 0; i < numTargets; i++) {
		int t = 0;
		for (int j = 0; j < targetOrder; j++)
			for (int k = j + 1; k < targetOrder; k++) {
				int val = rawTargets[i][t++];
				target[i][j][k] = val;
				target[i][k][j] = val;
			}
	}
}

void computeTargetDensities() {
	int lfact = fact(L);
	int normalizer = fact(targetOrder) * fact(L - targetOrder);
	for (int g = 0; g < numWordGraphs[L]; g++) {
		for (int p = 0; p < lfact; p++)
			for (int t = 0; t < numTargets; t++) {
				int good = true;
				for (int i = 0; i < targetOrder && good; i++)
					for (int j = i + 1; j < targetOrder && good; j++)
						if (target[t][i][j] != wordGraph[L][g][perm[L][p][i]][perm[L][p][j]])
							good = false;
				if (good)
					targetDensities[g]++;
			}
		targetDensities[g] /= normalizer;
	}
}

bool checkFlagIsomorphic(int t, int l, int i, int j) {
	int lfact = fact(l);
	for (int p = 0; p < lfact; p++) {
		bool good = true;
		for (int k = 0; k < l && good; k++)
			for (int m = 0; m < l && good; m++)
				if (k != m && (flagList[t][i][perm[l][p][k]][perm[l][p][m]] != flagList[t][j][k][m] || flagList[t][j][L][k] != flagList[t][i][L][perm[l][p][k]] ||
					flagList[t][j][L][m] != flagList[t][i][L][perm[l][p][m]]))
					good = false;
		if (good)
			return true;
	}
	return false;
}

void populateFlagList(int t, int l) {  // construct F_\ell^t. This will populate flagList[t], where flagList[t][i] is the l*l adjacency matrix or an order l flag, whose type index is t
	flagListSize[t] = 0;
	int ts = typeSize[t];
	int lfact = fact(l);
	// go over each graph in permGraph[l] and create all possible non-isomorphic flags from it.
	for (int g = 0; g < numWordGraphs[l]; g++) {
		int currLoc = flagListSize[t];
		// for each permutation \pi of l, try to see if vertices \pi[0]... \pi[ts-1] of current graph are isomorphic to the type
		for (int p = 0; p < lfact; p++) {
			bool good = true;
			for (int i = 0; i < ts; i++)
				for (int j = i + 1; j < ts; j++)
					if (wordGraph[l][g][perm[l][p][i]][perm[l][p][j]] != type[t][i][j])
						good = false;
			if (good) { // this is a valid flag; construct it and then check if it is isomorphic to any pervious flag
				for (int i = 0; i < l; i++)
					for (int j = 0; j < l; j++)
						flagList[t][flagListSize[t]][i][j] = wordGraph[l][g][i][j];
				for (int i = 0; i < l; i++)
					flagList[t][flagListSize[t]][L][i] = -1;
				for (int i = 0; i < ts; i++)
					flagList[t][flagListSize[t]][L][perm[l][p][i]] = i;
				// now check isimorphism with any pervious flag obtained from that graph
				int j;
				for (j = currLoc; j < flagListSize[t]; j++) // check if flagList[t][j] is isomorphic to flagList[t][flagListSize[t]]
					if (checkFlagIsomorphic(t, l, j, flagListSize[t]))
						break;
				if (j == flagListSize[t])
					flagListSize[t]++;
			}
		}
	}
}

void fillFlagLists() {
	for (int i = 0; i < numTypes; i++)
		populateFlagList(i, rawTypes[i][0] + (L - rawTypes[i][0]) / 2);
}

void populateMatrix(int g, int flagIndex, int l, int l1) {
	// g is the serial number of the graph of order l in the graph list; we are writing the constraints for this graph in SDarray[t][g]
	// flagIndex is the index of the flag list;  The flags in flagList[flagIndex] index the rows and column of the constriant matrix SDarray[t][g]
	// l is the size of the model graphs
	// l1 is the number of vertices of the flags in the flag list

	int k = rawTypes[flagIndex][0]; // order of the type; it should hold that k+(l1-k)+(l1-k) <= l

	// initialize to zero all the densities in the matrix
	for (int i = 0; i < flagListSize[flagIndex]; i++)
		for (int j = 0; j < flagListSize[flagIndex]; j++)
			SDarray[flagIndex][i][j] = 0;

	// loop over all permutations of vertices of H. For each permutation check if it induces a flag for the given type
	int lfact = fact(l);
	int l1fact = fact(l1);
	for (int p = 0; p < lfact; p++) {
		// check if the permutation perm[l][p] on the vertices of H induces the type  // e.g. if l=7, k=3 and the permutation is 43124506 then we check if the map 0->4 1->3 2->1 from th type to the graph induces the type 
		bool  good = true;
		for (int i = 0; i < k && good; i++)
			for (int j = i + 1; j < k && good; j++)
				if (wordGraph[l][g][perm[l][p][i]][perm[l][p][j]] != type[flagIndex][i][j])
					good = false;
		if (good) {
			// locate the flag  pair indices x,y isomorphic to vertices [0..k-1] \cup [k..l1-1] and [0..k-1] \cup [l1..l1+l1-k-1] and add to SDarray[t][g][x][y]
			int x = -1;
			int y = -1;
			// loop over all flags in flag list to locate x; there should be exactly one flag that is located (because the flags in the list are pairwise nonisomorphic)
			for (int f = 0; f < flagListSize[flagIndex]; f++) { // check if current flag f is isomorphic
				for (int p1 = 0; p1 < l1fact; p1++) {
					bool goodFlag = true;
					for (int i = 0; i < l1 && goodFlag; i++) {
						if (flagList[flagIndex][f][L][i] != -1 && flagList[flagIndex][f][L][i] != perm[l1][p1][i])
							goodFlag = false;
						for (int j = i + 1; j < l1 && goodFlag; j++) {
							int ind1 = perm[l][p][perm[l1][p1][i]];
							int ind2 = perm[l][p][perm[l1][p1][j]];
							if (flagList[flagIndex][f][i][j] != wordGraph[l][g][ind1][ind2])
								goodFlag = false;
						}
					}
					if (goodFlag)
						x = f;
				}
			}
			// loop over all flags in flag list to locate y; there should be exactly one flag that is located (because the flags in the list are pairwise nonisomorphic)
			for (int f = 0; f < flagListSize[flagIndex]; f++) { // check if current flag f is isomorphic
				for (int p1 = 0; p1 < l1fact; p1++) {
					bool goodFlag = true;
					for (int i = 0; i < l1 && goodFlag; i++) {
						if (flagList[flagIndex][f][L][i] != -1 && flagList[flagIndex][f][L][i] != perm[l1][p1][i])
							goodFlag = false;
						for (int j = i + 1; j < l1 && goodFlag; j++) {
							int i1 = 0, j1 = 0;
							if (perm[l1][p1][i] >= k) i1 = l1 - k;
							if (perm[l1][p1][j] >= k) j1 = l1 - k;
							int ind1 = perm[l][p][perm[l1][p1][i] + i1];
							int ind2 = perm[l][p][perm[l1][p1][j] + j1];
							if (flagList[flagIndex][f][i][j] != wordGraph[l][g][ind1][ind2])
								goodFlag = false;
						}
					}
					if (goodFlag)
						y = f;
				}
			}
			SDarray[flagIndex][x][y]++;
		}
	}
	int normalizer = fact(l1 - k) * fact(l1 - k);
	for (int i = 0; i < flagListSize[flagIndex]; i++)
		for (int j = 0; j < flagListSize[flagIndex]; j++)
			SDarray[flagIndex][i][j] /= normalizer;
}

void fillArrays(int g) {
	for (int i = 0; i < numTypes; i++)
		populateMatrix(g, i, L, rawTypes[i][0] + (L - rawTypes[i][0]) / 2);
}

void writeSDP(bool use_float, bool include_feasibility) {
	char fileName[20];
	FILE* sdpFile, * feasibilityFile = NULL;
	sprintf_s(fileName, "words%d.dat-s", W);
	fopen_s(&sdpFile, fileName, "w");
	if (include_feasibility) {
		sprintf_s(fileName, "feasibility%d.dat-s", W);
		fopen_s(&feasibilityFile, fileName, "w");
	}

	double target_normalizer = fact(targetOrder) * fact(L - targetOrder)/ (double)fact(L);
	double type_nomrlizer[maxNumTypes];
	for (int i = 0; i < numTypes; i++) {
		int k = rawTypes[i][0];
		int l1 = (rawTypes[i][0] + L) / 2;
		type_nomrlizer[i] = fact(L - l1) * fact(L - l1) / (double)fact(L);
	}

	int countValidFlags = 0;
	for (int i = 0; i < numTypes; i++)
		if (flagListSize[i] > 0)
			countValidFlags++;

	fprintf(sdpFile, "%d\n", numWordGraphs[L]); // first line contains the number of constraints
	if (include_feasibility)
		fprintf(feasibilityFile, "%d\n", numWordGraphs[L]);
	fprintf(sdpFile, "%d\n", countValidFlags + 1); // the number of blocks (corrsponds to the number of SD matrices plus one additional slack block
	if (include_feasibility)
		fprintf(feasibilityFile, "%d\n", countValidFlags + 1);

	for (int i = 0; i < numTypes; i++)
		if (flagListSize[i] > 0) {
			fprintf(sdpFile, "%d ", flagListSize[i]);  // writing the size of each block
			if (include_feasibility)
				fprintf(feasibilityFile, "%d ", flagListSize[i]);
		}
	fprintf(sdpFile, "%d\n", -numWordGraphs[L] - 1); // the size of the last block which is a diagonal block so preceded with a minus sign
	if (include_feasibility)
		fprintf(feasibilityFile, "%d\n", -numWordGraphs[L] - 1);

	// write the density in each graph as a list of numPermutationGraphs[L] numbers
	for (int i = 0; i < numWordGraphs[L]; i++) {
		if (use_float)
			fprintf(sdpFile, "%.11f ", targetDensities[i]*target_normalizer);
		else
			fprintf(sdpFile, "%d ", targetDensities[i]);
		if (include_feasibility)
			fprintf(feasibilityFile, "%d ", 0);
	}
	fprintf(sdpFile, "\n");
	if (include_feasibility)
		fprintf(feasibilityFile, "\n");

	// write the target line
	fprintf(sdpFile, "0 %d 1 1 1\n", countValidFlags + 1);

	// for each graph and for each block, write the nonzero entries
	for (int g = 0; g < numWordGraphs[L]; g++) {
		int c = -1;
		fillArrays(g);
		for (int t = 0; t < numTypes; t++) {
			if (flagListSize[t] > 0)
				c++;
			for (int i = 0; i < flagListSize[t]; i++)
				for (int j = i; j < flagListSize[t]; j++)
					if (SDarray[t][i][j] != 0) {
						if (use_float) {
							fprintf(sdpFile, "%d %d %d %d %.11f\n", g + 1, c + 1, i + 1, j + 1, SDarray[t][i][j]*type_nomrlizer[t]);
							if (include_feasibility)
								fprintf(feasibilityFile, "%d %d %d %d %.11f\n", g + 1, c + 1, i + 1, j + 1, SDarray[t][i][j]*type_nomrlizer[t]);
						}
						else {
							fprintf(sdpFile, "%d %d %d %d %d\n", g + 1, c + 1, i + 1, j + 1, SDarray[t][i][j]);
							if (include_feasibility)
								fprintf(feasibilityFile, "%d %d %d %d %d\n", g + 1, c + 1, i + 1, j + 1, SDarray[t][i][j]);
						}
					}
		}
		// write entriees for the slack block
		fprintf(sdpFile, "%d %d 1 1 1\n", g + 1, countValidFlags + 1);
		fprintf(sdpFile, "%d %d %d %d 1\n", g + 1, countValidFlags + 1, g + 2, g + 2);
		if (include_feasibility) {
			fprintf(feasibilityFile, "%d %d 1 1 1\n", g + 1, countValidFlags + 1);
			fprintf(feasibilityFile, "%d %d %d %d 1\n", g + 1, countValidFlags + 1, g + 2, g + 2);
		}
	}
	fclose(sdpFile);
	if (include_feasibility)
		fclose(feasibilityFile);
}

int main()
{
	loadPermutations();
	printf("Constructing word graphs...\n");
	constructGraphs();
	printWordGraphQuantities();
	loadTypes();
	loadTargets();
	computeTargetDensities();
	printf("Constructing flag lists...\n");
	fillFlagLists();
	printFlagListsQuantities();
	printf("Constructing input files for sdp solver...\n");
	writeSDP(false, false);
}