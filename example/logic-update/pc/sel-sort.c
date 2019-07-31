#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct Publication {
  char name[50];
  int pub_id;
  int rank;
} publication;

const char* readValue(char* string, int index)
{
    const char* token;
    for (token = strtok(string, ";");
            token && *token;
            token = strtok(NULL, ";\n"))
    {
        if (!--index)
            return token;
    }
    return NULL;
}

int sort(struct Publication pub_list[], int length) {
  int a, b, minimum, position;
  struct Publication selected;
  a = 0;
  while (a < length) {
    minimum = pub_list[a].rank;
    position = a;
    for (b = a + 1; b < length; b++) {
      if (pub_list[b].rank < minimum) {
        minimum = pub_list[b].rank;
        position = b;
      }
    }

    selected = pub_list[a];
    pub_list[a] = pub_list[position];
    pub_list[position] = selected;
    a++;
  }

  return 1;
}

int main(int argc, char const *argv[]) {
    struct Publication publications[5];
    FILE* stream = fopen(argv[1], "r");
    char line[1024];
    int i = 0;
    while (fgets(line, 1024, stream))
    {

        strcpy(publications[i].name, readValue(strdup(line), 1));
        publications[i].pub_id = atoi(readValue(strdup(line), 2));
        publications[i++].rank = atoi(readValue(strdup(line), 3));
    }

  sort(publications, 5);

  for (int i = 0; i < 5; i++)
    printf("%s\n", publications[i].name);

  return 0;
}
