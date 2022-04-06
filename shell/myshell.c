/*
 * --- A NOTE ON ACADEMIC HONESTY ---
 * The contents of this .c file were written by me,
 * Avery Kriegel, in 2017 as part of a project for
 * a computer science class.
 * 
 * I do not condone any form of plagerism or use of
 * this code for anyone who may be in said class.
 * 
 * If you suspect you may be in said class, please
 * do not view or copy any part of this file.
 */

#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
#include <sys/wait.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#define MAXLINE 1024

void myPrint(char *msg)
{
    write(STDOUT_FILENO, msg, strlen(msg));
}

typedef struct sll sll;
struct sll {
    char *first;
    sll *rest;
};

sll *sll_new(char *str, sll *list)
{
    if (str == NULL) {
	return list;
    }
    sll *result = (sll*)malloc(sizeof(sll));
    result->first = strdup(str);
    result->rest = list;
    return result;
}

void sll_free(sll *list)
{
    if (!list) {
	return;
    }
    sll_free(list->rest);
    free(list->first);
    free(list);
    return;
}

int sll_len(sll *list)
{
    int len = 0;
    while (list) {
	len++;
	list = list->rest;
    }
    return len;
}

void sll_show(sll *list)
{
    myPrint("list:\n");
    int len;
    while (list) {
	len = strlen(list->first);
	char buf[len+2];
	buf[0] = '\0';
	strcat(buf,list->first);
	buf[len] = '\n';
	buf[len+1] = '\0';
	myPrint(buf);
	list = list->rest;
    }
}

typedef struct {
    char **args;
    char *rd_path; //path to redirect file
    char *ard_path; //path to advanced redirect file
} cmd;

cmd *cmd_new(char *args[], char *rd, char *ard)
{
    if (!args) {
	return NULL;
    }
    cmd *result = (cmd*)malloc(sizeof(cmd));
    if (!result) {
    }
    result->args = args;
    if (rd) {
	result->rd_path = strdup(rd);
    } else {
	result->rd_path = NULL;
    }
    if (ard) {
	result->ard_path = strdup(ard);
    } else {
	result->ard_path = NULL;
    }
    return result;
}

void cmd_free(cmd *c)
{
    free(c->args);
    if (c->rd_path) {
	free(c->rd_path);
    }
    return;
}

void cmd_show(cmd *c)
{
    if (!c) {
	myPrint("cmd is NULL\n");
	return;
    }
    myPrint("cmd args:\n");
    char **args = c->args;
    int i = 0;
    while (args[i]) {
	printf("args[%d] = %s\n",i,args[i]);
	i++;
    }
    if (c->rd_path) {
	printf("rd_path = %s\n",c->rd_path);
    } else {
	printf("rd_path = NULL\n");
    }
    if (c->ard_path) {
	printf("ard_path = %s\n",c->ard_path);
    } else {
	printf("ard_path = NULL\n");
    }
} 

typedef struct cll cll;
struct cll {
    cmd *first;
    cll *rest;
};

cll *cll_new(cmd *command, cll *list)
{
    if (command == NULL) {
	return list;
    }
    cll *result = (cll*)malloc(sizeof(cll));
    result->first = command;
    result->rest = list;
    return result;
}

int cll_len(cll *list)
{
    int len = 0;
    while (list) {
	len++;
	list = list->rest;
    }
    return len;
}

void err()
{
    char error_message[30] = "An error has occurred\n";
    myPrint(error_message);
}

void cmd_exit()
{
    exit(0);
}

void cmd_pwd()
{
    char buf[MAXLINE];
    getcwd(buf, MAXLINE);
    myPrint(buf);
    myPrint("\n");
}

void cmd_cd(char* path)
{
    if (path) {
	if (chdir(path)) {
	    err();
	}
    } else {
	if (chdir(getenv("HOME"))) {
	    err();
	}
    }
}

void show_args(char *args[])
{
    if (!args) {
	myPrint("args is NULL\n");
	return;
    }
    int i = 0;
    myPrint("args:\n");
    while (args[i]) {
	myPrint(args[i++]);
	myPrint("\n");
    }
}

int is_built(char *args[])
{
    char *c = args[0];
    if (!strcmp(c,"exit")) {
	if (!args[1]) {
	    cmd_exit();
	    return 1;
	} else {
	    err();
	    return 1;
	}
    } else if (!strcmp(c,"pwd")) {
	if (!args[1]) {
	    cmd_pwd();
	    return 1;
	} else {
	    err();
	    return 1;
	}
    } else if (!strcmp(c,"cd")) {
	if (!args[1] || (args[1] && !args[2])) {
	    cmd_cd(args[1]);
	    return 1;
	} else {
	    err();
	    return 1;
	}
    } else {
	return 0;
    }
}

void cmd_exec(char *args[])
{
    if (is_built(args)) {
	return;
    }
    FILE *f = fopen(args[0], "r");
    int len = strlen(args[0]) + 10;
    int i;
    char buf[len];
    if (!f) {
	for (i = 0; i < len; i++) {
	    buf[i] = '\0';
	}
	strcat(buf, "/usr/bin/");
	strcat(buf, args[0]);
	f = fopen(buf, "r");
	if (!f) {
	    for (i = 0; i < len; i++) {
		buf[i] = '\0';
	    }
	    strcat(buf, "/bin/");
	    strcat(buf, args[0]);
	    f = fopen(buf, "r");
	    if (!f) {
		for (i = 0; i < len; i++) {
		    buf[i] = '\0';
		}
		strcat(buf, "./");
		strcat(buf, args[0]);
		f = fopen(buf, "r");
		if (!f) {
		    err();
		    return;
		}
	    }
	}
    }
    fclose(f);
    int forkret;
    int status;
    if ((forkret = fork()) == 0) {
	execvp(buf,args);
	}
    else {
	wait(&status);
    }
}

sll *parse_mult(char *input)
{
    char *str = strdup(input);
    sll *list = NULL;
    sll *comp = NULL;
    char *wtf_c = strtok(str,";\n");
    list = sll_new(wtf_c, list);
    while (1) {
	comp = list;
	list = sll_new(strtok(NULL,";\n"), list);
	if (comp == list) {
	    break;
	}
    }
    return list;
}

sll *str_to_sll(char *input)
{
    char *str = strdup(input);
    sll *list = NULL;
    sll *comp = NULL;
    char *wtf_c = strtok(str," \t");
    list = sll_new(wtf_c, list);
    while (1) {
	comp = list;
	list = sll_new(strtok(NULL," \t"), list);
	if (comp == list) {
	    break;
	}
    }
    return list;
}

char **sll_to_args(sll *list)
{
    if (!list) {
	return NULL;
    }
    int len = sll_len(list);
    char **args = (char**)malloc(sizeof(char*) * (len+1));
    if (!args) {
	return NULL;
    }
    args[len] = NULL;
    int i;
    for (i = len-1; i >= 0; i--) {
	args[i] = list->first;
	list = list->rest;
    }
    return args;
}

cmd *str_to_cmd(char *str)
{
    if (!str) {
	err();
	return NULL;
    }
    int i;
    char buf1[512];
    for (i = 0; i < 512; i++) {
	buf1[i] = '\0';
    }
    char buf2[512];
    for (i = 0; i < 512; i++) {
	buf2[i] = '\0';
    }
    int len = strlen(str);
    int rd = 0;
    int ard = 0;   
    for (i = 0; i < len; i++) {	
	if (str[i] == '>') {
	    if (rd || ard) {
		err();
		return NULL;
	    }
	    if (i+1 == len) {
		err();
		return NULL;
	    }
	    if (str[i+1] == '+') {
		if (i+2 == len) {
		    err();
		    return NULL;
		}
		ard++;
		strcat(buf2,&(str[i + 2])); 
	    } else {
		rd++;
		strcat(buf2,&(str[i + 1]));
	    }
	    strncat(buf1,str,i);
	}
    }
    if (!rd && !ard) {
	strcat(buf1,str);
    }
    sll *argsll = str_to_sll(buf1);
    if (rd || ard) {
	sll *rdpath = str_to_sll(buf2);
	if (sll_len(rdpath) != 1) {
	    err();
	    return NULL;
	}
	for (i = 0; i < 512; i++) {
	    buf2[i] = '\0';
	}
	strcat(buf2, rdpath->first);
    }
    char *rdp = (char*)buf2;
    char *ardp = (char*)buf2;
    if (!rd) {
	rdp = NULL;
    }
    if (!ard) {
	ardp = NULL;
    }
    char **args = sll_to_args(argsll);
    cmd *c = cmd_new(args, rdp, ardp);
    return c; 
}

cll *parse_input(char *input)
{
    sll *cmd_strs = parse_mult(input);
    cll *cmds = NULL;
    while (cmd_strs) {
	cmd *c = str_to_cmd(cmd_strs->first);
	if (c) {
	    cmds = cll_new(c, cmds);
	}
	cmd_strs = cmd_strs->rest;
    }
    return cmds;
}

int long_cmd(char buf[])
{
    return (buf[512] != '\n' && buf[512] != '\0');
}

int blank_line(char buf[])
{
    int i = 0;
    char c = buf[i];
    while (c != '\n' && c != '\0') {
	if (c != ' ' && c != '\t') {
	    return 0;
	}
	c = buf[++i];
    }
    return 1;
}

int cmd_rd(char *path)
{
    if (path) {
	if (fopen(path, "r")) {
	    err();
	    return -1;
	} else {
	    int tempfd = dup(STDOUT_FILENO);
	    int newfd = creat(path,S_IRWXU);
	    if (newfd == -1) {
		err();
		return -1;
	    }
	    dup2(newfd,1);
	    return tempfd;
	}
    }
    return 0;
}

int cmd_ard(char *path)
{
    if (path) {
	FILE *bees = fopen(path, "r+");
	if (bees) {
	    if (fopen("/tmp/advanced_mjolk","r")) {
		myPrint("you did it reddit\n");
		exit(0);
	    }
	    int mjolkfd = creat("/tmp/advanced_mjolk",S_IRWXU);
	    char bees_buff[512];
	    fgets(bees_buff, 512, bees);
	    while (!feof(bees)) {
		write(mjolkfd, bees_buff, strlen(bees_buff));
		fgets(bees_buff, 512, bees);
	    }
	    close(mjolkfd);
	    fclose(bees);
	    int tempfd = dup(STDOUT_FILENO);
	    int newfd = creat(path,S_IRWXU);
	    if (newfd == -1) {
		err();
		return -1;
	    }
	    dup2(newfd,1);
	    return tempfd;
	} else {
	    int tempfd = dup(STDOUT_FILENO);
	    int newfd = creat(path,S_IRWXU);
	    if (newfd == -1) {
		err();
		return -1;
	    }
	    dup2(newfd,1);
	    return tempfd;
	}
    }
    return 0;
}

void restore_stdout(int tempfd)
{
    dup2(tempfd, 1);
    return;
}

int is_rip(cmd *c) {
    if (c->rd_path || c->ard_path) {
	char *arg = c->args[0];
	if (!strcmp("cd", arg)) {
	    return 1;
	} else if (!strcmp("exit", arg)) {
	    return 1;
	} else if (!strcmp("pwd", arg)) {
	    return 1;
	}
    }
    return 0;
}

void run_batch(char *path)
{
    if (!path) {
	err();
	exit(0);
    }
    FILE *f = fopen(path, "r");
    if (!f) {
	err();
	exit(0);
    }
    char cmd_buff[514];
    char *pinput;
    int i;
    while(!feof(f)) {
	for (i = 0; i < 514; i++) {
	    cmd_buff[i] = '\n';
	}
	pinput = fgets(cmd_buff, 514, f);
	if (!pinput) {
	    exit(0);
	}
	if (long_cmd(cmd_buff)) {
	    while (long_cmd(cmd_buff)) {
		myPrint(cmd_buff);
		memset(cmd_buff, '\n', 514);
        	pinput = fgets(cmd_buff, 514, f);
        	if (!pinput) {
        	    exit(0);
        	}
	    }
	    myPrint(cmd_buff);
	    err();
	    continue;
	}
	if (blank_line(cmd_buff)) {
	    continue;
	}
	myPrint(cmd_buff);
	cll *cmds = parse_input(cmd_buff);
	int rd, ard;
	while (cmds) {
	    if (is_rip(cmds->first)) {
		err();
		cmds = cmds->rest;
		continue;
	    }
	    rd = cmd_rd(cmds->first->rd_path);
	    if (rd >= 0) {
		ard = cmd_ard(cmds->first->ard_path);
		if (ard >= 0) {
		    cmd_exec(cmds->first->args);
		    FILE *FrankerZ = fopen("/tmp/advanced_mjolk","r");
		    if (FrankerZ) {
			char mjolk_buff[512];
			fgets(mjolk_buff,512,FrankerZ);
			while(!feof(FrankerZ)) {
			    myPrint(mjolk_buff);
			    fgets(mjolk_buff, 512, FrankerZ);
			}
			fclose(FrankerZ);
		    }
		    if (rd || ard) {
			rd? restore_stdout(rd) : restore_stdout(ard);
			remove("/tmp/advanced_mjolk");
			remove("advanced_mjolk");
		    }
		}
	    }
	    cmds = cmds->rest;
	}
    }
}


int main(int argc, char *argv[]) 
{
    if (argc != 1) {
	if (argc != 2) {
	    err();
	    exit(0);
	} else {
	    run_batch(argv[1]);
	}
    }
    char cmd_buff[514];
    char *pinput;
    while (1) {
        myPrint("myshell> ");
	memset(cmd_buff, '\n', 514);
        pinput = fgets(cmd_buff, 514, stdin);
        if (!pinput) {
            exit(0);
        }
	if (long_cmd(cmd_buff)) {
	    while (long_cmd(cmd_buff)) {
		myPrint(cmd_buff);
		memset(cmd_buff, '\n', 514);
        	pinput = fgets(cmd_buff, 514, stdin);
        	if (!pinput) {
        	    exit(0);
        	}
	    }
	    myPrint(cmd_buff);
	    err();
	    continue;
	}
	if (blank_line(cmd_buff)) {
	    continue;
	}
	cll *cmds = parse_input(cmd_buff);
	int rd, ard;
	while (cmds) {
	    if (is_rip(cmds->first)) {
		err();
		cmds = cmds->rest;
		continue;
	    }
	    rd = cmd_rd(cmds->first->rd_path);
	    if (rd >= 0) {
		ard = cmd_ard(cmds->first->ard_path);
		if (ard >= 0) {
		    cmd_exec(cmds->first->args);
		    FILE *FrankerZ = fopen("/tmp/advanced_mjolk","r");
		    if (FrankerZ) {
			char mjolk_buff[512];
			fgets(mjolk_buff,512,FrankerZ);
			while(!feof(FrankerZ)) {
			    myPrint(mjolk_buff);
			    fgets(mjolk_buff, 512, FrankerZ);
			}
			fclose(FrankerZ);
		    }
		    if (rd || ard) {
			rd? restore_stdout(rd) : restore_stdout(ard);
			remove("/tmp/advanced_mjolk");
			remove("advanced_mjolk");
		    }
		}
	    }
	    cmds = cmds->rest;
	}
    }
}
