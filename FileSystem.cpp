#include<bits/stdc++.h>

using namespace std;

struct Data_block
{
 char data[1024];
};

struct block
{
  char name[8];
  int sizes;
  int blockPointers[8];
  int used = 0;
  
};

struct Super_Block
{
  char Is_empty[128];
  struct block index[16];
};

struct Super_Block super_block;
struct Data_block one_data_block[127];

//Create the file
void create_file(char name[], int size)
{
	//IS SPACE AVAILABLE ?
	int Is_space_available = -1;
    for(int i=0;i<16;i++)                             
    {
        if(super_block.index[i].used==0)
        {
           Is_space_available = i;
           break;
        }
    }

    if(Is_space_available==-1)
    {
      cout<<"No space available in the file system, can't create a new "<<name<<" file." << endl;
      return;
    }
	
	//CHECK TO HAVE UNIQUE FILENAME
    for(int i=0; i<16;i++)               
    {
       if((super_block.index[i].used==1)&&(strcmp(name,super_block.index[i].name) == 0))
       {
           cout<<" Sorry, Can't create the file with already existing name. File name should be unique." << name << endl;
           return;
       }
    }
	
	//IS THE TOTAL NUMBER OF BLOCKS REQUIRED EMPTY
    int no_of_block_available = 0;
    for(int i=1;i<128;i++)                   
    {
      if(super_block.Is_empty[i]=='0')
      no_of_block_available++;
    }

    if(no_of_block_available<size)
    {
       cout<<"The bolck size need to create the file " <<name<<" is not empty, Can't create the file" << endl;;
       return;
    }

    strcpy(super_block.index[Is_space_available].name, name);        
    super_block.index[Is_space_available].sizes = size ;
    int block_required=0;
    
    for(int i=1; block_required!=size; i++)
    {
        if(super_block.Is_empty[i]=='0')
        {
            super_block.Is_empty[i]='1';
            super_block.index[Is_space_available].blockPointers[block_required]=i;
            block_required++;
        }
    }
    
    //FILE CREATED SUCCESSFULLY
    super_block.index[Is_space_available].used=1;
    cout<<"File " <<name<<" Successfully created." << endl;

}

//READ THE FILE AT A PARTICULAR BLOCK
void read_file(char name[] , int blockNum, char buf[])                    
{
    for(int i=0; i<16;i++)
    {
    	if((super_block.index[i].used)&&(strcmp(name,super_block.index[i].name) == 0))
        {
        	if(blockNum>=super_block.index[i].sizes)
        	cout<<"Can't access the file as the number of blocks allocated is less than block number." << endl;
    	   else
        {
        	cout<<"Data from file "<<name<<" at blockumber "<<blockNum<<" is  "<<one_data_block[super_block.index[i].blockPointers[blockNum]].data<<endl;
        	strcpy(buf, one_data_block[super_block.index[i].blockPointers[blockNum]].data);
    	}
        	return;
        }
    }

    cout <<"File "<< name<<" doesn't exist, Can't read." << endl;
}

//WRITE THE FILE AT A PARTICULAR BLOCK
void write_file(char name[], int blockNum, char buf[])
{
    for(int i=0; i<16;i++)
    {
        if((super_block.index[i].used)&&(strcmp(name,super_block.index[i].name) == 0))
        {
        	if(super_block.index[i].sizes<=blockNum)
           		cout<<"Can't access the file as the number of blocks allocated is less than block number." << endl;
           	else
			{
           		strcpy(one_data_block[super_block.index[i].blockPointers[blockNum]].data,buf);
           		cout<<"Successfully written in the file" << endl;
			}
           	return;
        }
    }

    cout<<"File "<< name<<" doesn't exist, Can't write." << endl;

}

//LIST ALL THE FILE AND FILE SIZE
void list_all_file()
{
    for(int i=0;i<16;i++)
    {
        if(super_block.index[i].used==1)
        {
            cout<<"File name is = "<<super_block.index[i].name<<" and size of the file is = "<<super_block.index[i].sizes<<endl;
        }
    }
}

//DELETE THE FILE
void delete_file(char name[])                        
{
    for(int i=0; i<16;i++)               
    {
        if((super_block.index[i].used)&&(strcmp(name,super_block.index[i].name) == 0))
        {
           super_block.index[i].used=0;
           for(int j=0; j<super_block.index[i].sizes;j++)
           {
              super_block.Is_empty[super_block.index[i].blockPointers[j]]='0';
           }
           cout<<name<<" Successfully Deleted the file" << endl;
           return;
        }
    }
    cout<<"File "<< name<<" doesn't exist, Can't delete." << endl;
}


int main()
{   
    for(int i=0; i<128;i++)
    {
        super_block.Is_empty[i]='0';
    }
    
    int choice;
    do
    {
    	cout << "----------------------------------------------------------" << endl;
    	cout<<"Option 1: Create a file" << endl;
    	cout<<"Option 2: Read a file" << endl;
    	cout<<"Option 3: Write a file" << endl;
    	cout<<"Option 4: Delete a file" << endl;
    	cout<<"Option 5: Print all the file" << endl;
    	cout<<"Option 6: Exit" << endl;
    	cout<<"Enter the otion you want to choose = ";
    	
    	cin >> choice;
    	
    	switch(choice)
    	{
    		case 1: {
    			
    			cout<<"Please enter the name of file = ";
      			char str[8];
      			cin.ignore(256, '\n');
      			cin.getline(str, 8);
      			cout<<"Please enter the size of file = ";
      			int size;
      			cin>>size;
      			if(size>8)
      				cout<<"The bolck size entered is invalid, File size can't be more than 8" << endl;
      			else
      				create_file(str, size);
    			
				break;
			}
			
			case 2: {
				
				cout<<"Please enter the file name = ";
      			char str[8];
      			cin.ignore(256, '\n');
      			cin.getline(str, 8);
     		 	cout<<"Please enter the block number = ";
      			int block;
     			cin>>block;
      			char buf[1024];
      			read_file(str, block , buf);
      			
				break;
			}
			
			case 3: {
				
				cout<<"Please enter the file name = ";
      			char str[8];
      			cin.ignore(256, '\n');
      			cin.getline(str, 8);
      			cout<<"Please enter the block number = ";
     			int block;
      			cin>>block;
      			char buf[1024];
      			cout<<"Please enter the data you want to write in the file= ";
      			cin.ignore(256, '\n');
      			cin.getline(buf, 1024);
      			write_file(str, block , buf);
				
				break;
			}
			
			case 4: {
				
				cout<<"PLease enter the name of file = ";
      			char str[8];
      			cin.ignore(256, '\n');
      			cin.getline(str, 8);
      			delete_file(str);
      			
				break;
			}
			
			case 5: {
				
				list_all_file();
				
				break;
			}
			
			default :
				{}
			
		}
    	
		cout<<endl;
		cout << "----------------------------------------------------------------------" << endl << endl;
		
	}while(choice!=6);
    
	return 0;
}


