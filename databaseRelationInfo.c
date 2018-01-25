#include "stdio.h"
#include "stdlib.h"
#include "string.h"
#include "assert.h"

#define true 1
#define false 0

typedef char int8;
typedef unsigned char uint8;
typedef short int16;
typedef unsigned short uint16;
typedef int int32;
typedef unsigned int uint32;
typedef long long int int64;
typedef unsigned long long int uint64;

#define arr_length(a) (sizeof(a)/sizeof(a)[0])

#define printIntegerBinary(n, type)							\
{															\
	unsigned type powerof2 = 1 << (sizeof(type) * 8 - 1);	\
	while(powerof2) {										\
		if(n & powerof2)  {									\
			putchar('1');									\
		}else {												\
			putchar('0');									\
		}													\
															\
		powerof2 = powerof2 >> 1;							\
	}														\
															\
	putchar('\n');											\
}															\

#define USED_CHARACTER_RANGE 26//('Z' - 'A' + 1)

//skýra þetta x_attribute og y_attribute?
typedef struct functionalDependency {
	char *x;
	char *y;
} functionalDependency;

unsigned int hashNullTermString(const char *str) {
	unsigned int hash = 5381;

	for(unsigned char c; c = *str; str++) {
		//printf("%c\n", c);
		hash = (hash << 5) + hash + c;
	}

	return hash;
}

unsigned int hashStringInBuffer(const char **buffer_address) {
	char *buffer = *buffer_address;

	unsigned int hash = 5381;

	for(unsigned char c; c = *buffer; buffer++) {
		hash = (hash << 5) + hash + c;
	}

	*buffer_address = buffer;

	return hash;
}

void printKeyBuffer(char *buffer, size_t buffer_size, int do_print) {
	int string_end = false;	

	FILE *output;

	if(do_print) {
		output = stdout;
	}else {
		output = fopen("output.txt", "w");
	}

	for(int i = 0; i < buffer_size; i++) {
		if(buffer[i] == 0) {
			if(string_end) break;

			putc('\n', output);
			string_end = true;
		}else {
			putc(buffer[i], output);
			string_end = false;
		}
	}

	if(!do_print) fclose(output);
}

//kannski taka inn í reikninginn hvað relation-ið er stórt til þess að ákvarða hvað closure-ið getur orðið mögulega stórt
//það þarf samt þá líka að pæla í bókstöfunum
void attributeClosure(char *closure_buffer, char *attribute, functionalDependency *functional_set, size_t functional_count) {
	int closure_mask = 0;
	int attribute_len = strlen(attribute);
	int attribute_index = 0;

	while(attribute_index < attribute_len) {
		closure_mask = closure_mask | (1 << (attribute[attribute_index] - 'A')); 
		attribute_index++;
	}

	for(int i = 0; i < functional_count; i++) {
		char *x_attribute = functional_set[i].x;
		char *y_attribute = functional_set[i].y;
		
		int x_in_closure = true;

		for(int j = 0; j < strlen(x_attribute); j++) {
			if(!(closure_mask & (1 << (x_attribute[j] - 'A')))) {
				x_in_closure = false;
				break;	
			}
		}

		if(x_in_closure) {
			for(int j = 0; j < strlen(y_attribute); j++) {
				closure_mask = closure_mask | (1 << (y_attribute[j] - 'A')); 			
			}
		}
	}

	int closure_buffer_index = 0;

	for(int i = 0; i < sizeof(closure_mask) * 8; i++) {
		if(closure_mask & (1 << i)) {
			closure_buffer[closure_buffer_index] = 'A' + i;
			closure_buffer_index++;
		}
	}

	closure_buffer[closure_buffer_index] = 0;
}

void relationCandidateKeys(char *key_buffer, size_t key_buffer_size, char *relation, functionalDependency *functional_set, size_t functional_count) {
	int relation_length = strlen(relation);
	int key_hash[1 << relation_length];
	int key_hash_index = 0;
	char *key_buffer_point = key_buffer;
	int known_key_mask = -1;	//11111111...

	for(int i = 0; i < functional_count; i++) {
		char *y_attribute = functional_set[i].y;
		char c;

		while((c = *y_attribute)) {
			int index = c - 'A';
		
			if(known_key_mask & (1 << index)) {
				known_key_mask = known_key_mask ^ (1 << index);	
			}

			y_attribute++;
		}
	}

	char known_key_part[relation_length + 1];
	memset(known_key_part, 0, relation_length + 1);
	{
		int known_key_part_index = 0;

		for(int i = 0; i < relation_length; i++) {
			int index = relation[i] - 'A';
			
			if(known_key_mask & (1 << index)) {
				known_key_part[known_key_part_index] = relation[i];
				known_key_part_index++;
			}
		}
	}

	if(strcmp(relation, known_key_part) == 0) {
		strcpy(key_buffer, known_key_part);
		return;
	}else {
		char known_key_part_closure[relation_length + 1];
		memset(known_key_part_closure, 0, relation_length + 1);
		attributeClosure(known_key_part_closure, known_key_part, functional_set, functional_count);

		if(strcmp(relation, known_key_part_closure) == 0) {	
			strcpy(key_buffer, known_key_part);
			return;	
		}
	}

	int bit_length;//meira lýsandi nafn, þ.e.a.s hafa það í samhengi við breytuna sem það er skilgreint út frá
	char unknown_part[relation_length + 1];
	memset(unknown_part, 0, relation_length + 1);
	{
		int unknown_part_index = 0;

		for(int i = 0; i < relation_length; i++) {
			if(~known_key_mask & (1 << i)) {
				unknown_part[unknown_part_index] = relation[i];
				unknown_part_index++;
			}
		}

		 bit_length = 1 << unknown_part_index;
	}

	char possible_key[relation_length + 1];
	memset(possible_key, 0, relation_length + 1);
	char *permutation_part = stpcpy(possible_key, known_key_part);

	for(unsigned int i = 0; i < bit_length; i++) {
		int index = 0;
		int permutation_part_index = 0;
		memset(permutation_part, 0, (relation_length + 1) - (permutation_part - possible_key));

		for(unsigned int j = 1; j < bit_length; j = j << 1) {
			if(i & j) {
				permutation_part[permutation_part_index] = unknown_part[index];
				permutation_part_index++;
			}

			index++;
		}

		char possible_key_closure[relation_length + 1];
		memset(possible_key_closure, 0, relation_length + 1);
		attributeClosure(possible_key_closure, possible_key, functional_set, functional_count);

		//printf("%s: %s\n", possible_key, possible_key_closure);
		
		if(strcmp(relation, possible_key_closure) == 0) {
			unsigned int possible_key_hash = hashNullTermString(possible_key);

			for(char *key_in_buffer = key_buffer; *key_in_buffer != 0 && *(key_in_buffer + 1) != 0; key_in_buffer++) {
				int key_in_buffer_hash = hashStringInBuffer(&key_in_buffer);
			}

			key_buffer_point = stpcpy(key_buffer_point, possible_key) + 1;
			assert((key_buffer_point - key_buffer) <= key_buffer_size);
		}
	}

	//setja það í buffer og síðan check-a hvort að einhver lykill í bufferinu sé hlutmengi í þeim mögulega mögulega lykil sem verið er að skoða
}

void relationSuperKeys(char *relation, functionalDependency *functional_set, size_t functional_count) {
	//öll subset-in sem innihalda lyklana
}

void powerSet(const char *str) {
	int set_length = strlen(str);
	int bit_length = 1 << set_length;

	for(unsigned int i = 0; i < bit_length; i++) {
		int index = 0;

		for(unsigned int j = 1; j < bit_length; j = j << 1) {
			if(i & j) {
				putchar(str[index]);
			}

			index++;
		}

		putchar('\n');
	}
}

void printCandidateKeys(char *relation, functionalDependency *functional_set, size_t functional_count) {
	//buffer þarf max að vera (n C (n/2)) * strlen(relation) + n (+n fyrir 0-in)
	int relation_length = strlen(relation);

	size_t buffer_size = (1 << relation_length) * relation_length + relation_length;
	char *buffer = (char *)malloc(buffer_size);
	memset(buffer, 0, buffer_size);

	printf("%d\n", buffer_size);

	relationCandidateKeys(buffer, buffer_size, relation, functional_set, functional_count);
	printKeyBuffer(buffer, buffer_size, true);

	free(buffer);
}

int main() {
	
	#if 0
		functionalDependency f[] = {(functionalDependency){"AEF", "C"},
									(functionalDependency){"BF", "C"},
									(functionalDependency){"EF", "D"},
									(functionalDependency){"ACDE", "F"}};

		printCandidateKeys("ABCDEF", f, arr_length(f));
		//powerSet("ABC");
	#endif

	#if 1
		functionalDependency f[] = {(functionalDependency){"A", "B"},
									(functionalDependency){"B", "A"},
									(functionalDependency){"C", "D"},
									(functionalDependency){"D", "C"},
									};

		printCandidateKeys("ABCD", f, arr_length(f));
	#endif

	#if 0
		functionalDependency f[] = {(functionalDependency){"A", "B"},
									(functionalDependency){"B", "A"},
									(functionalDependency){"C", "D"},
									(functionalDependency){"D", "C"},
									(functionalDependency){"E", "F"},
									(functionalDependency){"F", "E"}
									};

		printCandidateKeys("ABCDEF", f, arr_length(f));
	#endif
	
	#if 0
		functionalDependency f[] = {(functionalDependency){"B", "E"},
									(functionalDependency){"B", "A"},
									(functionalDependency){"CE", "B"},
									(functionalDependency){"C", "D"},
									};

		printCandidateKeys("ABCDE", f, arr_length(f));
	#endif

	#if 0
	functionalDependency f[] = {(functionalDependency){"A", "B"},
								(functionalDependency){"B", "A"},
								(functionalDependency){"C", "D"},
								(functionalDependency){"D", "C"},
								(functionalDependency){"E", "F"},
								(functionalDependency){"F", "E"},
								(functionalDependency){"G", "H"},
								(functionalDependency){"H", "G"},
								(functionalDependency){"I", "J"},
								(functionalDependency){"J", "I"},
								(functionalDependency){"K", "L"},
								(functionalDependency){"L", "K"},
								(functionalDependency){"M", "N"},
								(functionalDependency){"N", "M"},
								(functionalDependency){"O", "P"},
								(functionalDependency){"P", "O"}
								};

	printCandidateKeys("ABCDEFGHIJKLMNOP", f, arr_length(f));
	#endif

	#if 0
	functionalDependency f[] = {(functionalDependency){"AB", "C"},
	 							(functionalDependency){"CD", "E"},
	 							(functionalDependency){"EF", "G"},
	 							(functionalDependency){"FG", "E"},
	 							(functionalDependency){"DE", "C"},
	 							(functionalDependency){"BC", "A"}
								};

	printCandidateKeys("ABCDEFG", f, arr_length(f));
	#endif
	

	return 0;
}