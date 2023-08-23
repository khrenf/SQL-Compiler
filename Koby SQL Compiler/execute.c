/*execute.c*/

//
// Project: Execution of queries for SimpleSQL
//
// Koby Renfert
// Northwestern University
// CS 211, Winter 2023
//
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>  // true, false
#include <string.h>   // strcpy, strcat
#include <assert.h>   // assert
#include "tokenqueue.h"
#include "scanner.h"
#include "parser.h"
#include "ast.h"
#include "database.h"
#include "util.h"
#include "analyzer.h"
#include "execute.h"
#include "resultset.h"
#include <strings.h>

// limitClause allows the user to only output a certain amount of data. ex: limit 3 will show no more than 3 entries. 
void limitClause(struct ResultSet* rs, struct SELECT* select);

// execute_query
// 
// Conduct a select query, with other possible SQL keywords. Opens an underlying file and sourts through the data building a resultset structure. Based on the input this resultset will be modified to ultimately only display the information you want. Without any specified modifications it will return all information applying to the entered query
//

void execute_query(struct Database* db, struct QUERY* query)
{
  if (db == NULL) panic("db is NULL (execute)");
  if (query == NULL) panic("query is NULL (execute)");

  if (query->queryType != SELECT_QUERY)
  {
    printf("**INTERNAL ERROR: execute() only supports SELECT queries.\n");
    return;
  }

  struct SELECT* select = query->q.select;  // alias for less typing:

  //
  // the query has been analyzed and so we know it's correct: the
  // database exists, the table(s) exist, the column(s) exist, etc.
  //

  //
  // (1) we need a pointer to the table meta data, so find it:
  //
  struct TableMeta* tablemeta = NULL;

  for (int t = 0; t < db->numTables; t++)
  {
    if (icmpStrings(db->tables[t].name, select->table) == 0)  // found it:
    {
      tablemeta = &db->tables[t];
      break;
    }
  }
  
  assert(tablemeta != NULL);
  struct ResultSet* rs;
  rs = resultset_create();
  
  for (int i = 0; i < tablemeta->numColumns; i++) {
    resultset_insertColumn(rs, i + 1, tablemeta->name, tablemeta->columns[i].name, NO_FUNCTION, tablemeta->columns[i].colType);
  }
  // resultset_print(rs);
  // above loop finds the table that we are targeting
  // now we want to iterate through each column of that table

  // 
  // (2) open the table's data file
  //
  // the table exists within a sub-directory under the executable
  // where the directory has the same name as the database, and with 
  // a "TABLE-NAME.data" filename within that sub-directory:
  //
  char path[(2 * DATABASE_MAX_ID_LENGTH) + 10];

  strcpy(path, db->name);    // name/name.data
  strcat(path, "/");
  strcat(path, tablemeta->name);
  strcat(path, ".data");

  FILE* datafile = fopen(path, "r");
  if (datafile == NULL) // unable to open:
  {
    printf("**INTERNAL ERROR: table's data file '%s' not found.\n", path);
    panic("execution halted");
  }

  //
  // (3) allocate a buffer for input, and start reading the data:
  //
  int   dataBufferSize = tablemeta->recordSize + 3;  // ends with $\n + null terminator
  char* dataBuffer = (char*)malloc(sizeof(char) * dataBufferSize);
  if (dataBuffer == NULL) panic("out of memory");

  // Step 4 opens the inputted data file and reads its data into the resultset structure we created. Uses fgets to continue reading data until EOF is reached, at which point the loop is broken. Data lines are broken into mini-strings, of which each is stored in a certain type of column (ex: "Forest Gump" goes with 'title').
  while (!feof(datafile))
  {
    if (fgets(dataBuffer, dataBufferSize, datafile) != NULL){
      char* cp = dataBuffer;
      char* stringStart = dataBuffer;
      int i = 0;
      int rowNumb = resultset_addRow(rs);
      bool inquote = false;
      char startQuote = '\'';
      //within for loop check the type 
      for (cp = dataBuffer; *cp != '\0'; cp++) { 
        if ((*cp == '"' || *cp == '\'') && inquote == false) {
          startQuote = *cp;
          inquote = true;
          }
        else if (*cp == startQuote && inquote == true) { 
          inquote = false;
          }
        
        else if (*cp == ' ' && !inquote) {
          *cp = '\0';
          int type = tablemeta->columns[i].colType;
          if (type == 1) { //int
            int intvar = atoi(stringStart);
            resultset_putInt(rs, rowNumb, i + 1, intvar);
            }
          if (type == 2) { //real
            double doubreal = atof(stringStart);
            resultset_putReal(rs, rowNumb, i + 1, doubreal);
            }
          if (type == 3) { //string
            char* pointcp = cp - 1;
            *pointcp = '\0';
            stringStart++;
            resultset_putString(rs, rowNumb, i + 1, stringStart);
            }
          stringStart = cp + 1;
          i++;
          }
        }
    }
  }

  // Step 6 impliments where capabilities. select->where checks for a where clause in the input query. Proceed if true. Decides to what the where clause refers to. Ex "... where ID > 100" compares all row values for the column it refers to, to the value 100, using the operator (in this case >). Will then output all xx data with an ID > 100.
  if (select->where != NULL) {
    char* targetWord = (select->where->expr->column->name);
    double difference = 0; //finding the difference between the values being compared
    
    for (int i = rs->numRows; i > 0; i--) { 
      int targetCol = resultset_findColumn(rs, 1, tablemeta->name, targetWord);
      int targetType = (tablemeta->columns[targetCol - 1].colType); // check back
      //if/elses to determine which type we're looking at 
      if (targetType == COL_TYPE_INT) {
        int colValue = resultset_getInt(rs, i, targetCol);
        int value = atoi(select->where->expr->value);
        difference = colValue - value;
      }
        
      else if (targetType == COL_TYPE_REAL) {
        double colValue = resultset_getReal(rs, i, targetCol);
        double value =  atof(select->where->expr->value);
        difference = colValue - value;
      }
        
      else if (targetType == COL_TYPE_STRING) {
        char* colValue = resultset_getString(rs, i, targetCol);
        char* target = (select->where->expr->value);
        difference = strcmp(colValue, target);
        free(colValue);
      }

      // Now check what to do based on each operator and the diff value
      if (select->where->expr->operator == EXPR_LT && difference >= 0) {
        resultset_deleteRow(rs, i);
      }
      else if (select->where->expr->operator == EXPR_LTE && difference > 0) {
        resultset_deleteRow(rs, i);
      }
      else if (select->where->expr->operator == EXPR_GT && difference <= 0) {
        resultset_deleteRow(rs, i);
      }
      else if (select->where->expr->operator == EXPR_GTE && (difference < 0)) {
        resultset_deleteRow(rs, i);
      }
      else if (select->where->expr->operator == EXPR_EQUAL && difference != 0) {
        resultset_deleteRow(rs, i);
      }
      else if (select->where->expr->operator == EXPR_NOT_EQUAL && difference == 0)       {
        resultset_deleteRow(rs, i);
      }
    } // ends main if
  }

  //Step 7 checks which columns we previously added are not requested when there is a select phrase and deletes them. Example, "select ID from" will only print the ID column of each entry and no others.
  for (int i = 0; i < tablemeta->numColumns; i++ ) { 
    bool unwantedCol = true;
    struct COLUMN* cur = select->columns;
    
    while (cur != NULL) {
      if (strcasecmp(tablemeta->columns[i].name, cur->name) == 0) {
        unwantedCol = false;
        break;
      }
      else {
        cur = cur->next;
      }
    }
  if (unwantedCol) {
    resultset_deleteColumn(rs, resultset_findColumn(rs, 1, tablemeta->name, tablemeta->columns[i].name));
    }
  }

  // Step 8 allows us to output the columns in the correct order. Example, output from "select ID, Title" is not the same as output from "select Title, ID". We do this by locating the position in the result set of each requested column and moving them to be in the desired order based on the input query (using resultset_findColumn)'s output as input for moveColumn function.
  struct COLUMN* cur1 = select->columns;
  int c = 1;
  while (cur1 != NULL) {
    int colLoc = resultset_findColumn(rs, 1, tablemeta->name, cur1->name);
    resultset_moveColumn(rs, colLoc, c);
  c++;
    cur1 = cur1->next;
  }

  // Step 9 applies min, max etc functions if requested using the given resultset_applyFunction. 
  struct COLUMN* cur = select->columns;
  int i = 0;
  while (cur != NULL) {
    if (cur->function != NO_FUNCTION) {
      resultset_applyFunction(rs, cur->function, i + 1);
    }
    cur = cur->next;
    i++;
  }

  // Step 10 unlocks the limit clause. Ex ".. limit 5" means we only have the first 5 entries in the resultset. Does this by finding the amount of rows and deleting until the number of rows = the number requested by limit.

  limitClause(rs, select);

  
  fclose(datafile);
  free(dataBuffer);
  resultset_print(rs);
  resultset_destroy(rs);
}

//definition for part 10
void limitClause(struct ResultSet* rs, struct SELECT* select) {
  if (select->limit != NULL) {
    int lim = select->limit->N;
    while(rs->numRows > lim) { 
      resultset_deleteRow(rs, lim + 1);
    }
  }
}