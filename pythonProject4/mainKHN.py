#블록체인
#트랜잭션은 항상 이전과 현재 트랜잭션이 연결되어있다.
#현재 블록은 이전 블록의 정보를 항상 가지고 있다.
#트렌젝션 (거래정보) 들을 모아 블록을 생성한다.

#헤더에는 메타정보 (보통 해시정보 등) 이 들어간다.
#바디에는 실제거래정보 / 센서정보/ 성적정보등이 들어가게된다.

import hashlib #보안 및 메세지 요약 알고리즘 인터페이스
import time #날짜 시간 모듈
import csv #csv 파일 컨트롤 모듈
import random
from http.server import BaseHTTPRequestHandler, HTTPServer #서버 띄우기 위한 라이브러리
from socketserver import ThreadingMixIn #네트워크 서버 작성 작업 단순 (클래스는 동기적으로 요청을 처리..느리다.. 요청을 처리하기 위해 별도의 프로세스나 스레드를 만들자!ThreadingMixIn 믹스인 클래스를 사용하여 비동기 동작을 지원)
import json # JSON 문자열을 읽거나, HTTP 요청의 전문(body)을 읽을 때 자주 사용 , Python 객체를 JSON 문자열로 변환하기 위해서는 dumps() 함수를 사용
import re #정규표현식
from urllib.parse import parse_qs
from urllib.parse import urlparse #url 파싱 라이브러리 (문자열을 구성요소로 분리)
#여러분이 사용하는 PC에는 윈도우, macOS, 리눅스와 같은 운영체제가 설치되어 있습니다. 운영체제는 컴퓨터를 전체적으로 관리하는 매니저 역할을 합니다. 우리가 프로그램이라고 부르는 것들은 운영체제 위에서 동작합니다. 프로그램이 메모리에 올라가서 실행 중인 것을 프로세스(process)라고 부릅니다. 프로세스의 실행 단위를 스레드라고 합니다. 프로세스는 최소 하나 이상의 스레드를 갖으며 경우에 따라 여러 스레드를 가질 수도 있습니다.
import threading #스레드 컨트롤 #교수님이 말씀하셨던 중국집을 생각해보자. 요리를 하는 스레드 주문을 받는 스레드, 병렬처리를 위한 많은 스레드들이 필요하다. -> 하나의 프로세스 안에서 스레드가 분리되는 것이지 프로그램이 여러개 돌아가는 느낌은 아니다
import cgi #웹서버와 언어간의 쉬운 연동을 위한 표준화된 약속 > cgi(common gateway interface)
import uuid #universally unique identifier #가장 유일한 번호구하기
from tempfile import NamedTemporaryFile #임시파일/디렉토리 생성 모듈  TemporaryDirectory 자동 정리를 제공하고 컨텍스트 관리자로 사용할 수 있음. 임시 저장 영역으로 사용할 수 있는 파일류 객체를 반환
import shutil #파일 및 디렉터리 작업을 수행
import requests #ython에서 HTTP 요청을 보내는 모듈 -> 내 소스에서 외부 서버에 접솔할 때 (ㅍ스트맨이 내 서버에 접속하는 것 처럼 내가 다른 서버에 것 포스트 등등을 날릴 때 사용하는 라이브러리 # for sending new block to other nodes
import pandas as pd

#프로세스를 만들어주는 라이브러리
#프로세스가 서로 간섭하지 않도록 Lock 객체를 사용 -> 어떤 자원에 두 스레드가 동시에 사용하려고 할 때 먼저 락을 선점하려고 .acquire()를 호출 할 것이다. 선점한 스레드는 자원을 사용할 수 있다, 하지만 같이 사용하려고 접근하던 다른 스레드의 진행은 멈추게 되고 선점한 스레드가 자원의 사용을 마치고 lock.release()를 호출하여 풀어줬을 때 그제서야 사용할 수 있게된다.
# for using Lock method(acquire(), release())
from multiprocessing import Process, Lock
# for Put Lock objects into variables(lock)
lock = Lock()

PORT_NUMBER = 8666 #포트넘버 정의
g_txFileName = "txData.csv" #트랜잭션데이터 파일
g_bcFileName = "blockchain.csv" #블록체인 파일
g_nodelstFileName = "nodelst.csv" #여러 서버로 채굴을 할 때 인접 노드를 미리 등록해주는 것
g_receiveNewBlock = "/node/receiveNewBlock"
g_difficulty = 5 #난이도 정의
g_maximumTry = 100 #최대 시도 횟수
g_nodeList = {'127.0.0.1':'8668'}  #인접 노드를 하드코딩으로 정의 # trusted server list, should be checked manually

#블록을 만드는 클래스 -> 6개의 생성자를 가지고 블록이라는 객체를 생성한다
class Block: #블록 클래스 클래스 안에 작은 모듈들이 들어가게됨
    #init ->초기화 메서드 # 어떤 클래스의 객체가 만들어질 때 자동으로 호출되어 그 객체가 갖게될 여러가지 성질을 정의
    #이제 블록 객체를 만들 때는 인잇을 통해 정의한 파라미터들을 넘겨줘야한다.
    def __init__(self, index, previousHash, timestamp, data, currentHash, proof ): #인덱스, 이전해시값, 시간, 데이터, 현재해시값, 작업증명 (비잔틴 장군을 떠올려보자)
        self.index = index
        self.previousHash = previousHash #항상 인접 정보의 해시를 가지고있다가 비교해주어야함
        self.timestamp = timestamp
        self.data = data
        self.currentHash = currentHash
        self.proof = proof #작업증명 값 -> 채굴을 위해 몇번을 시도했는지?

    # 파이썬 객체를 제이슨 형식으로 파싱함 #default -> 값이 입력되지 않으면 디폴트값 자동 입 # 람다 -> 인자:표현식 함수와 비슷하다고 생각하면 됨 인풋값:식 #__dict__ -> a = b 라는 객체를 {a:b}로 변경
    def toJSON(self):
        return json.dumps(self, default=lambda o: o.__dict__, sort_keys=True, indent=4)

class txData: #트랜잭션 데이터 클라스

    def __init__(self, commitYN, sender, amount, receiver, uuid): #커밋여부, 전송자, 전송량?, 수신자, 고유 식별자
        self.commitYN = commitYN
        self.sender = sender
        self.amount = amount
        self.receiver = receiver
        self.uuid =  uuid

#제너레이트 블록 생성 함수 - 최초의 블럭 -> 임의의 트랜잭션을 내부에서 생성, 해시함수를 통해 난이도에 만족하는 해시값이 나올 때 까지 계쏙 돌려서 제너레이트 블럭한다. 블록이 생성되면 리턴해준다.
def generateGenesisBlock():
    print("generateGenesisBlock is called") #호출하면 안내문 출력
    timestamp = time.time() #시간 가지고와 타임스탬프 변수에 저장
    print("time.time() => %f \n" % timestamp)
    tempHash = calculateHash(0, '0', timestamp, "Genesis Block", 0)  #해시계산 함수(시간정보, 제네시스 블록을 파라미터로 넣어줌)로 받아온 임시해시값을 tempHash변수에 넣어줌
    print(tempHash)
    return Block(0, '0', timestamp, "Genesis Block",  tempHash,0) # 위에서 받아온 해시값을 이용해 제네시스 블록을 생성. 0번째 블록이 생성되었다.

def calculateHash(index, previousHash, timestamp, data, proof): # 해시값 계산 함수 (새로 생성)
    value = str(index) + str(previousHash) + str(timestamp) + str(data) + str(proof) #받아온 파라미터들을 문자열로 변환해 모두 value 변수 안에 넣어줌
    sha = hashlib.sha256(value.encode('utf-8')) # 생성한 문자열을 해시 함수를 돌려 해시값 생성 후 리턴
    return str(sha.hexdigest())

def calculateHashForBlock(block): # 현재의 해시값에는 이전의 해시값들이 포함되어야한다. 그래서 파라미터로 전달받은 블록의 해시값을 계산한다.
    return calculateHash(block.index, block.previousHash, block.timestamp, block.data, block.proof)

def getLatestBlock(blockchain): # 블록체인의 가장 마지막 블록을 가지고 오는 함수
    return blockchain[len(blockchain) - 1] #블록체인의 길이 -1 -> 마지막 인덱스를 통해 가지고 온 뒤 리턴해준다.
#다음 블록 채굴 함수
#데이터 (트랜잭션)이 들어갈 블록을 만들자. 다음 블록 생성 함수 (전체블록체인, 블록데이터, 시간, 작업증명) #블록을 생성하기 위해선 더 많은 파라미터가 있어야하는데 갯수가 적다! 부족한 부분은 안에서 정의하자.
def generateNextBlock(blockchain, blockData, timestamp, proof):
    previousBlock = getLatestBlock(blockchain) # 프리비어스 블록 = 위에서 정의한 함수를 호출해 가지고 온 블록체인의 마지막 블록
    nextIndex = int(previousBlock.index) + 1 # 현재 블록의 마지막 인덱스 +1 로 다음 블록의 인덱스를 지정해줌
    nextTimestamp = timestamp #nextTimestammp = 파라미터로 들어온 시간
    nextHash = calculateHash(nextIndex, previousBlock.currentHash, nextTimestamp, blockData, proof) #다음 해시값 = 파라미터가 다 준비되었으니 calculateHash함수를 호출하자! 그러면 리턴으로 해시값을 준다!
    # index, previousHash, timestamp, data, currentHash, proof
    return Block(nextIndex, previousBlock.currentHash, nextTimestamp, blockData, nextHash,proof) #generateNextBlock의 리턴으로 블록 객체 생성( 위에서 구한 인덱스, 마지막블록의 해시값, 인풋받은 시간, 블록데이타, 다음해시값(지금생성하는 블록의 해시값), 작업증명)


# 20190605 / (YuRim Kim, HaeRi Kim, JongSun Park, BohKuk Suh , HyeongSeob Lee, JinWoo Song)
# /* WriteBlockchain function Update */
# If the 'blockchain.csv' file is already open, make it inaccessible via lock.acquire()
# After executing the desired operation, changed to release the lock.(lock.release())
# Reason for time.sleep ():
# prevents server overload due to repeated error message output and gives 3 seconds of delay to allow time for other users to wait without opening file while editing and saving csv file.

#블록을 csv파일로 작성하는 함수 -> 채굴한 블록들을 파일로 쓰려고 하는데 객체는 파일로 작성할 수 없다. 단순 문자열만 가능! 그래서 포문을 돌며 객체를 문자열로 변환하는 작업을 해준다.
#왜 추가하지않고 다 가지고와서 덮어쓰는 걸까? 그냥 쓰다가 다 날아가면 큰일이 난다! 그래서 기존 파일을 백업을 뜨고 전체적으로 다시 써준다
def writeBlockchain(blockchain): #함수 외부에서 블록체인을 파라미터로 받아온다 -> 난이도르르 만족시킬 경우 작성!

    blockchainList = [] #빈 리스트 정의 ->블록체인 리스트는 밖에서 파라미터로 받아온 블록체인에대한 정보를 담아주는 변수이다.

    for block in blockchain: #외부에서 받아온 블록체인의 요소 하나씩 가지고오기

        blockList = [block.index, block.previousHash, str(block.timestamp), block.data, block.currentHash,block.proof ] #블록리스트라는 리스트 변수에 한 블록이 가지고 있는 정보들을 넣기
        blockchainList.append(blockList) #블록체인리스트 변수에 방금 생성한 블록 리스트 어팬드해주기. 블록체인리스트는 다중배열이 되어있을 것.

    #[STARAT] check current db(csv) if broadcasted block data has already been updated
    try: #파일 읽기 시도 / 블록체인 파일을 읽기모드로 읽어옴 밑에서부터는 file이라고 명명, #newline=''을 지정하지 않으면, 따옴표 처리된 필드에 포함된 줄 넘김 문자가 올바르게 해석되지 않 newline=''을 지정하는 것이 안전
        with open(g_bcFileName, 'r',  newline='') as file:
            blockReader = csv.reader(file) #블록체인리더(리스트) = csv형태인 블록체인 파일을 읽은 것(우리에게 저장되어있는 csv파일을 읽어온 것)
            last_line_number = row_count(g_bcFileName) #last_line_number = 블록체인의 행 수를 읽은 것 ( 0번째 블록을 포함 몇개의 블록이 존재하는지 알 수 있음 )
            for line in blockReader: #블록리더 (블록체인 파일)에서 한 줄씩을 가지고 옴 / 블록체인파일의 수가 마지막 행 숫자와 같아지면 (즉 , for 문의 마지막에 다다르면)
                if blockReader.line_num == last_line_number: # last블록 변수에 파일 마지막 줄의 블록정보 (#인덱스, 이전해시값, 시간, 데이터, 현재해시값, 작업증명)를 담아준다
                    lastBlock = Block(line[0], line[1], line[2], line[3], line[4], line[5])


        # 이 이프문은 여러 서버로 블록을 채굴할 경우에 생길 수 있는 예외를 정의했다. 만약 내가 블록을 채굴했다. 그리고 이제 그 정보를 csv파일에 저장하려고 한다. csv파일에 새로운 블록에 대한 정보를 쓰려면 새로운 인덱스가 필요하다.
        # 내가 채굴한 블록이 5번째 블록이라고 하자. 아직 나는 csv파일에 블록 정보를 쓰지 못했기때문에 파일의 마지막 인덱스는 4일것이다. 그러면 내가 쓸려는 5번째 인덱스를 csv파일에 쓰려면 4+1 인 5가 내가 작성하려는 인덱스의 정보가 될것이다.
        # 정상적인 경우라면 내가 채굴한 블록 (5번째)의 숫자와 내가 파일로 작성하려는 숫자(5번째를 채굴했다고 작성해야하니까) 는 같아야 할 것이다.
        # 그런데 만약 내가 작성하려는 인덱스와 내가 채굴한 블록의 숫자가 같지 않다면?? 누군가 나보다 먼저 블록을 채굴해서 이미 파일에 업로드를 해버린 것이다. 몇개를 업로드 했는지는 아직 알 수 없다. 그럼 내가 채굴한 블록은 더이상 사용하지 못할 것이다.
        # 그럴 때 우선 인덱스 시퀀스 미스매치 안내문을 출력한다.
            # 그런데 위의 조건을 만족하면서 동시에 '내가 채굴한 블록정보' 와 csv파일의 마지막 블록정보의 숫자가 같다면?
            # 누군가가 나와 간발의 차이로 똑같이 5번째 블록을 채굴했는데, 나보다 먼저 파일에 업로드를 해버린 것이다.
            # 나는 5번 블록을 채굴했는데, 누군가 파일에 5번 블록에 대한 정보를 업로드해버렸다.
            # 이런 경우 파일의 마지막 인덱스 == 내가 체굴한 블록 인덱스 인 것이다. 그런 경우 "블록체인이 이미 업데이트되었습니다" 출력에 하는 것 ( 조금 더 자세한 정보를 출력하기 위해서 )
        # 이런 예외에 걸린 경우 writeBlockChain함수는 더이상 의미가 없음으로 리턴값으로 함수에서 빠져나온다.
        if int(lastBlock.index) + 1 != int(blockchainList[-1][0]):
            print("index sequence mismatch")
            if int(lastBlock.index) == int(blockchainList[-1][0]):
                print("db(csv) has already been updated")
            return
    except: #파일을 읽는데 실패한 경우 안내문 출력한 후 패스
        print("file open error in check current db(csv) \n or maybe there's some other reason")
        pass
        #return
    # [END] check current db(csv)
    openFile = True #오픈 파일이라는 변수에 거짓 값을 넣어준다.
    while openFile: #오픈 파일이 참인 경우 반복문 실행
        if blockchainList != []: #블록체인리스트가 비어있지 않다면,
            try:#뭔가를 시도해보자
                lock.acquire()#락 선점을 시도했다.
                with open(g_bcFileName, "w", newline='') as file: #블록체인csv파일을 쓰기모드로 읽어온다. (쓰기 모드로 열 시 파일이 존재하지 않으면 파일 생성 / 존재한다면 기존 내용이 다 사라지고 새로 작성 / 만약 기존 데이터를 지키고 새로 작성하고싶다면 a 옵션을 주자)
                    writer = csv.writer(file) #파일 작성을 위한 변수에 할당
                    writer.writerows(blockchainList) #csv파일에 블록체인 리스트를 작성해준다.
                    blockchainList.clear() #블록체인 리스트 초기화 / 잘 작성되었다는 안내문구 출력
                    print("write ok")
                    openFile = False # 오픈 파일을 트루로 변경
                    for block in blockchain: #블록체인에 존재하는 행 하나하나를 가지고오기
                        updateTx(block) #트랜젝션을 업데이트 할 수 있는 함수 호출, 파라미터로 블록을 넣어준다.
                    print('Blockchain written to blockchain.csv.') #블록체인이 파일로 작성되었다는 안내문구 출력
                    print('Broadcasting new block to other nodes') #브로드캐스팅 하겠다는 것을 알려준다.
                    broadcastNewBlock(blockchain) #브로드캐스트 함수를 호출해 다른 노드들에게 브로드캐스트로 블록체인 채굴을 알린다
                    lock.release()  #자원의 점유를 풀어준다.
            except: #선점에 실패한 경우 혹은 파일을 여는데 실패한 경우 3초대기 후 실패에대한 안내문구 출력 한 뒤 자원 선점을 풀어준다
                    time.sleep(3) #선점에 실패할 수도 있는데 풀어주는 이유는, 에러가 난 경우에는 선점에 성공한건지 실패한건지 명확하게 알 수 없기 때문에 일단 풀어주는 것
                    print("writeBlockchain file open error")
                    lock.release()
        else: #블록체인 리스트가 비어있다면 비어있다는 안내문구 출력
            print("Blockchain is empty")
#블록이 존재하는지 /하지않는지 확인하고 블록을 읽는 함수
#트라이 문으로 파일 열기 시도, 에러나면 (없다면?) 익셉트 문으로 빠짐! -> 그 안의 모드가 인터널 일 때는? 제네시스 블록을 호출한다 (블록이 하나도 없으니 0번째 블록을 만들자!) -> 인터널 값은 내부의 필요에 의해 쓰여지는 값이구나!
def readBlockchain(blockchainFilePath, mode = 'internal'): #블록이 존재한다면? 블록을 읽어라 존재하지 않는다면, 제네시스 블록을 생성하여 마인 뉴 블록 함수에 전달
    # #블록체인파일 경로를 파라미터로 받아온다. 디폴트값 없기때문에 파라미터 들어와야함 / 모드는 디폴트값이 있어 호출시 없어도 가능. 여기서 모드는 내부 값을 가져오는 듯 하다.
    print("readBlockchain") #블록체인 읽어온다는 안내문구 출력 후 빈 배열을 하나 설정해준다.
    importedBlockchain = []

    try: #파일 읽어오기 시도 성공했을 경우
        with open(blockchainFilePath, 'r',  newline='') as file: #파일을 읽기 모드로 연다 new line이 개행문자 구분해줘서 라인바이라인으로 읽음 읽어서 file에 넣자.
            blockReader = csv.reader(file) #읽어온 파일을 블록리더 변수에 넣어준다. 여기서 블록리더의 타입은 리스트이다
            for line in blockReader: #포문을 돌며 읽어온 컬럼 하나하나를 블록으로 생성함.
                block = Block(line[0], line[1], line[2], line[3], line[4], line[5]) #블록이라는 변수 안에 읽어온 라인의 정보 (블록정보) 를 넣어준 뒤 블록리더(빈 배열에) 한줄씩 어팬드해준다.
                importedBlockchain.append(block) # [ ㅁ, ㅁ, ㅁ, ㅁ, ㅁ, ㅁ ]

        print("Pulling blockchain from csv...") #csv에서 블록체인을 땡겨온다.

        return importedBlockchain #완성된 배열을 리턴값으로 돌려준다. (이 배열에는 csv파일에 업로드 되어있는 모든 블록의 정보가 들어있을 것)

    except: #파일을 읽어오는 것을 실패했을 경우
        if mode == 'internal' : #모드가 인터널인 경우 -> 인터널 - 내부적으로 필요에 의해서 호출된거고 그 외에는 엘스문으로 들어감 보통은 위의 트라이 문에서 끝난다. (이라인은 보통 제네시스 블록을 호출할 때만 사용)
            blockchain = generateGenesisBlock() # 블록체인이라는 변수에 제네시스 블록 함수를 호출한다. (그럼 블록체인이라는 배열에는 0번째 제네시스 블록이 생성되어있는 상태일 것이다.)
            importedBlockchain.append(blockchain) #try문에 들어가지 못했기 때문에 지금 importBlockChain 은 빈 배열일 것이다. 그곳에 0번째 블록인 제네시스 블록을 넣어준다.
            writeBlockchain(importedBlockchain) #제네시스 블록이 들어가있는 importBlockChain 변수를 writeBlockChain 함수에 파라미터로 넣어준다. 만약 문제가 없다면 csv 파일로 작성될 수 있을 것이다.
            return importedBlockchain #임포트 블록체인 변수를 리턴값으로 반환해준다.
        else : #모드가 인터널이 아니라면, 리턴값은 아무것도 없다.
            return None

def updateTx(blockData) : #트랜잭션을 업데이트 해주는 함수 블록 데이터를 파라미터로 받는다.

    phrase = re.compile(r"\w+[-]\w+[-]\w+[-]\w+[-]\w+") #정규표현식 사용을 위해 re 라이브러리를 불러왔다. 식이 기니 변수에 넣어주 # [6b3b3c1e-858d-4e3b-b012-8faac98b49a8]UserID hwang sent 333 bitTokens to UserID kim.
    matchList = phrase.findall(blockData.data) #인풋값으로 받은 블록데이터.데이터 중에 정규표현식과 같은 형태의 데이터들을 모주 찾아온다. 찾아온 아이들을 매치리스트라는 변수에 넣어줌
    if len(matchList) == 0 : #만약 일치하는 값이 없어 matchList의 길이가 0이라면, 매치되는 것을 찾지 못했다는 안내 문구를 출력 (블록 데이터와 블록 인덱스를 함께 출력해줌) 후 함수 빠져나오기
        print ("No Match Found! " + str(blockData.data) + "block idx: " + str(blockData.index))
        return

    tempfile = NamedTemporaryFile(mode='w', newline='', delete=False) #tempfile = 임시파일 생성 모듈 호출 , 쓰기모드, 개행문자 구분, 자동삭제값 False

    with open(g_txFileName, 'r') as csvfile, tempfile: #트랜젝션 데이터 파일 열기 , 두개의 변수에 각각 담아준다. tempfile 은 임시파일이 변수에 담겨있는 상태이다.
        reader = csv.reader(csvfile) #트랜잭션 데이터를 읽어와 reader에 임시파일에 작성하는 부분은 writer변수에 담아준다.
        writer = csv.writer(tempfile)
        for row in reader: #일기파일에서 한 행씩 가지고 오기
            if row[4] in matchList: #만약 가지고 온 행 (블록) 의 4번째 정보가 매치리스트에 존재한다면, 행을 업데이트한다는 안내문구 출력 후 그 행의 0번째 정보를 1로 바꿔준다.
                print('updating row : ', row[4])
                row[0] = 1
            writer.writerow(row) #임시 파일에 그 행을 추가해줌

    shutil.move(tempfile.name, g_txFileName) #shutil라이브러리 - 파일 및 디렉토리 작업을 수행하는 라이브러리) -> 임시파일의 이름을
    csvfile.close() #두 파일 다 닫아주고 트랜잭션 데이터가 업데이트 됐음을 알린다.
    tempfile.close()
    print('txData updated')

# 20190605 /(YuRim Kim, HaeRi Kim, JongSun Park, BohKuk Suh , HyeongSeob Lee, JinWoo Song)
# /* writeTx function Update */
# If the 'txData.csv' file is already open, make it inaccessible via lock.acquire()
# After executing the desired operation, changed to release the lock.(lock.release())
# Reason for time.sleep ():
# prevents server overload due to repeated error message output and gives 3 seconds of delay to allow time for other users to wait without opening file while editing and saving csv file.
# Removed temp files to reduce memory usage and increase work efficiency.
def writeTx(txRawData): #트렌잭션을 작성하기위한 함수 정의. 호출 시 트랜젝션 데이터가 들어온다 (아마 새로운 트랜젝션의 데이터가 들어오는 듯 함)
    print(g_txFileName) #먼저 트랜잭션데이터 파일 이름을 출력해준다 / 빈 배열 두개를 설정
    txDataList = []
    txOriginalList = []
    for txDatum in txRawData: #파라미터로 받아온 새로운 트랜잭션데이터 요소를 한 행씩 꺼내온다. / txList 변수에 [꺼내온 한 행의 정보 (커밋여부, 송신자, 양, 수신자, 고유번호)] 를 담아준다.
        txList = [txDatum.commitYN, txDatum.sender, txDatum.amount, txDatum.receiver, txDatum.uuid]
        txDataList.append(txList) #가지고 온 정보들을 트랜잭션 데이터 리스트에 넣어준다.

    try: #트랜잭션 데이터 파일 열기 시도 / 파일을 읽어 reader변수에 넣어준다.
        with open(g_txFileName, 'r', newline='') as csvfile:
            reader = csv.reader(csvfile)
            for row in reader: #읽어온 트랜잭션 데이터 파일을 한 행씩 가지고 온다.
                txOriginalList.append(row) #txOriginalList에 읽어온 트랜잭션 데이터의 행들을 추가해준다.

            openWriteTx = False #변수값을 false로 설정해준다.
            while not openWriteTx: #변수가 거짓일 때 while문 실행 / 스래드가 loc 선점 시도
                lock.acquire()
                try: #자원의 점유를 알리고 트랜젝션 데이터 파일을 열어준다. 이번에는 쓰기모드로 설정
                    print("NewTxData lock.acquire")
                    with open(g_txFileName, 'w', newline='') as csvfile:
                        writer = csv.writer(csvfile)
                        # adding new tx
                        writer.writerows(txOriginalList) #트랜잭션 데이터 파일에 행을 추가해준다 ( 읽어온 트랜잭션 데이터 파일 )
                        writer.writerows(txDataList) #트랜잭션 데이터 파일에 새로운 트랜잭션 정보를 추가해줌(우리가 이 함수 호출 시 파라미터로 받아온 값)
                        print("writeTx write ok")
                        csvfile.close() #파일 닫기
                        openWriteTx = True #변수 값을 트루로 바꿈 (이제 더이상 while문에 들어오지 않는다)
                        lock.release() #점유를 해제

                except Exception as e: #읽기성공 +쓰기 실패일 경우 이 except문으로 들어온다. 실패했을 경우 안내문구 출력 후 자원 점유 해제. (아래에서 다시 한 번 쓰기를 시도하게 됨)
                    print(e)
                    time.sleep(3)
                    print("file open error")
                    lock.release()
    except: #읽기모드에 실패했을 경우 다시 한번 파일을 쓰기모드로 여는 것을 시도해보고 새로운 트랜잭션 데이터를 행으로 작성해준다
        # this is 1st time of creating txFile
        try:
            with open(g_txFileName, "w", newline='') as file:
                writer = csv.writer(file)
                writer.writerows(txDataList)
        except: #읽기모드 실패 + 쓰기모드 실퍠 = 리턴값을 0으로
            return 0
    return 1 #아닌경우(읽기/쓰기 둘 다 성공한 경우) 리턴값은 1
    print('txData written to txData.csv.')

def readTx(txFilePath): #트랜잭션 데이터를 읽어오는 함수 정의. 안내문구 출력 후 빈 배열을 잡아준다.
    print("readTx")
    importedTx = []

    try: #파라미터로 들어온 파일을 읽기모드로 열기 시도
        with open(txFilePath, 'r',  newline='') as file:
            txReader = csv.reader(file)
            for row in txReader: #읽어온 파일을 한 행씩 가지고 온다
                if row[0] == '0': #읽어온 행의 맨 앞 요소가 0일 경우 -> 라인이라는변수에 txData 클래스를 호출하고 행의 정보들을 넣어준다.  # find unmined txData
                    line = txData(row[0],row[1],row[2],row[3],row[4])
                    importedTx.append(line) #변수에 담겨있는 txData 객체를 importedTx리스트에 넣어준다. 리스트에는 각 행의 0번째 요소가 0인 데이터들만 들어가 있게 됨
        print("Pulling txData from csv...") #안내문구 출력
        return importedTx #리턴값으로 맨 앞이 0인 데이터들이 담겨있는 리스트 반환.
    except: #파일 읽기에 실패했을 경우에는 그냥 빈 배열 리턴
        return []

def getTxData(): #트렌젝션 생성 -> 블록에 들어갈 문자열을 만들어라!  # 먼저 빈 배열을 정의해준다.
    strTxData = ''
    importedTx = readTx(g_txFileName) #트랜잭선 정보가 들어있는 파일을 읽어와 변수에 넣어준다.
    if len(importedTx) > 0 : #만약 트랜잭션 정보가 존재한다면?
        for i in importedTx: #그 정보를 하나씩 가지고 오자
            print(i.__dict__) # 정보를 딕셔너리 형태로 바꿔 출력해준다 /  아래의 transactin 문자열에 담겨있는 값은 현재 "[고유번호값] UserId 전송자 sent 전송량 bitTokens to userID 수신자."
            transaction = "["+ i.uuid + "] UserID " + i.sender + " sent " + i.amount + " bitTokens to UserID " + i.receiver + ". "
            print(transaction) #위의 정보를 담아둔 문자열 출력
            strTxData += transaction #위에 정의해둔 빈 문자열에 우리가 담아준 트랜잭션 정보 밀어넣기

    return strTxData #트랜잭션 정보를 담고있는 문자열을 리턴값으로 돌려줌

#블록 채굴 함수 - 난이도에 맞는 값이 나올 때 까지 와일문을 돌며 다음 블록을 만드는 함수를 계속해서 소출한다.파라미터 주지 않아도 여기서 설정한 디폴트값이 들어감 -> 블록채인을 채굴하고 싶어! 블록체인이 이미 존재한다면 거기에 채굴해서 추가하고 , 없다면 새로 만들면 되겠다! 그렇다면 있는지 없는지 확인하기 위 리드블록체인 함수 호출!
def mineNewBlock(difficulty=g_difficulty, blockchainPath=g_bcFileName):
    blockchain = readBlockchain(blockchainPath) # 블록체인 패스가 뭐야.. 할수도 있지만 잘 보면 위에서 디폴트 값으로 블록체인패스라는 변수 안에 블록체인 파일 명이 들어가있다. 결국 블록체인 파일 이름을 파라미터로 주고 함수를 호출한 것 정상적인 경우라면 readBlockChain 함수에서 리턴값으로 배열을 반환해주었을 것이다. 그 값을 변수에 담자
    strTxData = getTxData() #getTxData함수 실행 , 만약 정상적으로 실행이 됐다면 트랜잭션 정보를 담고있는 문자열을 리턴값으로 주었을 것이다.
    if strTxData == '' : #만약 그 변수 값이 빈 값이라면 (정상적으로 블록체인 파일을 읽어오지 못했다면) 트랜잭선 정ㅈ보를 찾지 못했다는 안내문구 출력 후 함수 탈출
        print('No TxData Found. Mining aborted')
        return

    timestamp = time.time() #트랜잭션 정보가 존재한다면(위의 if문에 걸리지 않는다면) 타임스탬프 변수에 현재 시간을 담아준다
    proof = 0 #작업증명 값 0으로 설정하고 newBlockFound 값은 false로 설정 / 블록을 채굴중이라는 안내문구 출력
    newBlockFound = False #변수를 생성해준다.

    print('Mining a block...')

    while newBlockFound: #while문 진입 / newBlockAttempt 변수에 기존블럭에 이어서 새 블록을 만들 수 있는 함수를 호출해준다.
        newBlockAttempt = generateNextBlock(blockchain, strTxData, timestamp, proof) #(블록체인, 트랜잭션데이터, 시간, 작업증명 값을 파라미터로 넣어준다) 이렇게 넣어주면 이 함수에서는 부족한 파라미터를 생성해 (해시값 등) 6개의 파라미터를 채워 Block 클래스를 호출하고 파라미터 값이 블록에 저장됨으로서 새로운 블록이 탄생하게 될 것이다.
        if newBlockAttempt.currentHash[0:difficulty] == '0' * difficulty: #새 블록의 현재 해시값[인덱스 0부터: 난이도로 정의한 값(연속으로 0이 몇개가 나와한다는 값)] 이  "0" * 난이도의 개수와 같다면 (만약 같지 않다면 새 블록은 유효하지 않다)
            stopTime = time.time() #현재시간 변수 설정
            timer = stopTime - timestamp #타이머라는 변수에 현재시간 - 위에서 정의한 timeStamp 값을 빼준다.
            print('New block found with proof', proof, 'in', round(timer, 2), 'seconds.')
            newBlockFound = True #이제 while문에는 진입하지않는다
        else: #아닌경우에 작업증명 값에 1을 더해준다.
            proof += 1

    blockchain.append(newBlockAttempt) #블록체인에 새로 생성된 블록을 추가해줌
    writeBlockchain(blockchain) #writeBlockChain함수를 호출하고 블록체인을 파라미터로 넣어준다 ( 위에서 살펴본 것 처럼 내가 채굴한 블록이 누군가가 먼저 채굴하지 않았다면 csv파일에 업로드되고 성공적으로 채굴이 마무리 될 것이다)

def mine(): #이 함수를 호출하면 함수 내부에서 다시 mineNewBlock을 호출해준다.
    mineNewBlock()

def isSameBlock(block1, block2): #파라미터로 들어온 두개의 블록이 같은 블록인지 판별하는 함수 블록 두개의 값을 파라미터로 받아와 함수를 정의
    if str(block1.index) != str(block2.index): #두개의 인덱스 / 이전해시값 / 데이터 / 현재해시값 / 작업증명 값 중 하나라도 같지 않다면 False를 리턴
        return False
    elif str(block1.previousHash) != str(block2.previousHash):
        return False
    elif str(block1.timestamp) != str(block2.timestamp):
        return False
    elif str(block1.data) != str(block2.data):
        return False
    elif str(block1.currentHash) != str(block2.currentHash):
        return False
    elif str(block1.proof) != str(block2.proof):
        return False
    return True #위의 예시에 하나도 걸리지 않을 경우 ( 즉 두 블록이 모든 정보가 같은 블록일 경우 ) True 값을 리턴해준다.

def isValidNewBlock(newBlock, previousBlock): #블록이 유효한지 판단해주는 함수 ( 새 블록, 이전블록 ) 을 파라미터로 받는다
    if int(previousBlock.index) + 1 != int(newBlock.index): #이전블록의 인덱스 + 1이 새 블록의 값과 같지 않다면 ( 인덱스가 잘못되었다는 이야기!) 그렇다면 맞지 않다는 안내문구 출력
        print('Indices Do Not Match Up')
        return False #false값 반환
    elif previousBlock.currentHash != newBlock.previousHash: #이전 블록의 현재 해시값이 새블록의 과거 이전 해시값과 같지 않은 경우 ( 새 블록의 이전 해시 == 과거 블록의 현재 해시 ) 라는 공식이 성립해야 정상적인 블록이라고 할 수 있다.
        print("Previous hash does not match")
        return False #해시값이 일치하지 않는다는 안내문구 출력 후 거짓 리턴
    elif calculateHashForBlock(newBlock) != newBlock.currentHash: #calculateHashForBlock 함수에 파라미터로 새블록을 넣어준다. 거기서 나온 해시값이 새로운 블록의 현재 해시값과 다르다면 ? 이 또한 정상적인 블록이 아니다. 그렇다면 해시값이 유효하지 않다는 안내문구 출력.
        print("Hash is invalid")
        return False
    elif newBlock.currentHash[0:g_difficulty] != '0' * g_difficulty: #새 블록의 현재 해시값[인덱스 0부터: 난이도로 정의한 값(연속으로 0이 몇개가 나와한다는 값)] 이  "0" * 난이도의 개수와 같지 않다면 이것도 유효하지 않은 해시값이다. 해시 난이도가 적절하지 않다는 안내문구 출력
        print("Hash difficulty is invalid")
        return False
    return True

#새로운 트랜직션 생성 함수
#트랜잭션은 누가 누구에게 얼마를 줬다는 문자열이다. 트랜잭션들을 쌓아놨다가 채굴할 때 블록에 포함시키게된다. 채굴안된경우 [0]컬럼이 0 / 채굴된 경우 1이된다.
#서버가 밖에서 들어온 문자열을 다 파싱해서 이 함수를 호출하면, 함수는 그 자료를 가지고 트랜잭션 데이터라는 객체르 생성하고 그 객체를 가지고 writeTx 함수를 호출하게된다.
def newtx(txToMining):

    newtxData = []
    # transform given data to txData object
    for line in txToMining: #파라미터로 들어온 정보를 한 행씩 불러옴
        tx = txData(0, line['sender'], line['amount'], line['receiver'], uuid.uuid4()) #트랜잭션 클라스 호출. 파라미터로 라인에서 가지고 온 정보를 넣어줌. 생성된 트랜잭션을 변수에 할당
        newtxData.append(tx)  #트랜잭션을 리스트에 추가해줌

    # limitation check : max 5 tx
    if len(newtxData) > 5 : #트랜잭션의 갯수가 5개보다 많을 경우 -> 트랜잭션 한계를 초과했다는 안내문구 출력한 뒤 -1 리턴
        print('number of requested tx exceeds limitation')
        return -1

    if writeTx(newtxData) == 0: #트랜젝션이 0개일 경우 -> 파일을 작성하지 못했다는 안내문구 출력 후 -2 리턴
        print("file write error on txData")
        return -2
    return 1 #if문에 해당되지 않을 경우 (정상적으로 실행된 경우) -> 1 리턴

def isValidChain(bcToValidate): #체인 검증 함수
    genesisBlock = [] #제네시스 블록 리스트 / 블록 검증 리스트 생성
    bcToValidateForBlock = []

    # Read GenesisBlock
    try: #블록체인 csv파일 열기 시도
        with open(g_bcFileName, 'r',  newline='') as file:
            blockReader = csv.reader(file)
            for line in blockReader: #파일의 한 행씩 불러와 한 행의 요소 하나하나를 블록 클래스의 파라미터로 넣어줌
                block = Block(line[0], line[1], line[2], line[3], line[4], line[5]) #블록 변수에 생성된 블록을 넣어준다
                genesisBlock.append(block) #제네시스 블록 리스트에 추가해준다
#                break
    except: #파일을 열지 못했을 경우 파일 오픈 에러 안내문구 출력 / 거짓 리턴
        print("file open error in isValidChain")
        return False

    # transform given data to Block object
    for line in bcToValidate: #파라미터로 들어온 데이터를 한 행씩 불러옴
        # print(type(line))
        # index, previousHash, timestamp, data, currentHash, proof
        block = Block(line['index'], line['previousHash'], line['timestamp'], line['data'], line['currentHash'], line['proof']) #블록 클래스에 행의 요소를 호출 블록 클래스에 넣어준다. 생성된 블록을 블록 변수에 할당
        bcToValidateForBlock.append(block) #블록 검증 리스트에 추가해줌

    #if it fails to read block data  from db(csv)
    if not genesisBlock: #제네시스 블록이 없을 경우 실패 안내 / 거짓 값 리턴
        print("fail to read genesisBlock")
        return False

    # compare the given data with genesisBlock
    if not isSameBlock(bcToValidateForBlock[0], genesisBlock[0]): #제네시스 블록 리스트와 검증 블록 리스트의 0번째 블록이 서로 같지 않을 경우 제네시스 블록이 일치하지 않는다는 문구 출력 /거짓 값 리턴
        print('Genesis Block Incorrect')
        return False

    # tempBlocks = [bcToValidateForBlock[0]]
    # for i in range(1, len(bcToValidateForBlock)):
    #    if isValidNewBlock(bcToValidateForBlock[i], tempBlocks[i - 1]):
    #        tempBlocks.append(bcToValidateForBlock[i])
    #    else:
    #        return False

    for i in range(0, len(bcToValidateForBlock)): #검증 블록의 길이만큼 포문 돌기
        if isSameBlock(genesisBlock[i], bcToValidateForBlock[i]) == False: #만약 검증리스트의 블록과 제네시스리스트의 블록 중 하나라도 다른 것이 있다면 거짓 값 리턴
            return False

    return True #위의 조건들에 모두 해당하지 않는다면 참 값 리턴

# 20190605 / (YuRim Kim, HaeRi Kim, JongSun Park, BohKuk Suh , HyeongSeob Lee, JinWoo Song)
# /* addNode function Update */
# If the 'nodeList.csv' file is already open, make it inaccessible via lock.acquire()
# After executing the desired operation, changed to release the lock.(lock.release())
# Reason for time.sleep ():
# prevents server overload due to repeated error message output and gives 3 seconds of delay to allow time for other users to wait without opening file while editing and saving csv file.
# Removed temp files to reduce memory usage and increase work efficiency.
def addNode(queryStr): #노드를 추가하는 함수 정의 //배열을 파라미터로 받아옴?
    # save
    previousList = [] #빈 배열 설정
    nodeList = []
    nodeList.append([queryStr[0],queryStr[1],0]) #노드 리스트에 함수 호출 시 들어온 파라미터의 0,1 번째 인덱스, 0 값을 노드리스트 변수에 저장  # ip, port, # of connection fail

    try:
        with open(g_nodelstFileName, 'r', newline='') as csvfile:
            reader = csv.reader(csvfile) #노드 리스트 파일 읽어오기
            for row in reader: #읽어온 파일의 한 행씩 가지고오기
                if row: #그 값이 참이라면   (존재한다면)
                    if row[0] == queryStr[0] and row[1] == queryStr[1]: # 파일로 저장되이있는 노드 리스트와 함수에 파라미터로 들어온 노드의  각 0번째 1번째 인덱스가 같다면
                        print("requested node is already exists") #요청한 노드는 이미 존재한다는 안내문구 출력한 뒤 파일 닫아주기
                        csvfile.close()
                        nodeList.clear() #이미 존재하는 노드임으로 이제 쓸 필요가 없다 . 노드리스트 비워주고 -1 리턴
                        return -1
                    else: #리스트에 존재하지 않는 노드라면 ?
                        previousList.append(row) #비어있는 previous 배열에 노드 리스트 파일에서 읽어온 행 추가하기

            openFile3 = False #변수 값 거짓으로 설정
            while not openFile3: #변수 값이 거짓인동안 while문 실행
                lock.acquire() #선점 시도
                try:
                    with open(g_nodelstFileName, 'w', newline='') as csvfile: #노드리스트 파일을 쓰기 모드로 읽어오기 시도
                        writer = csv.writer(csvfile) #파일에 쓸 준비해 변수에 넣어주기
                        writer.writerows(nodeList) #노드리스트에 추가되어있는 값을 노드리스트 파일에 행으로 써준다
                        writer.writerows(previousList) #프리비어스 리스트에 있는 항목도 노드리스트에 추가해준다
                        csvfile.close() #파일 닫이주고 자원 점유 해제 , 노드리스트 비워줌
                        nodeList.clear()
                        lock.release()
                        print('new node written to nodelist.csv.') #정삭적으로 작성되었다는 안내문구출력 후 1 리턴
                        return 1
                except Exception as ex: #쓰기모드 예외처리  #파일 작성에 실패한 경우 에러 코드 출력 3초 후 안내문구 출력 / 점유 해제
                    print(ex)
                    time.sleep(3)
                    print("file open error")
                    lock.release()

    except: #읽기모드 예외처리
        # this is 1st time of creating node list
        try: #노드 리스트 파일을 읽기 모드로 불러온다
            with open(g_nodelstFileName, "w", newline='') as file:
                writer = csv.writer(file)
                writer.writerows(nodeList) #노드리스트 배열을 파일에 작성
                nodeList.clear() #파일 닫아주고 새로운 노드를 작성하였다는 안내문구 출력 리턴 값 1 반환
                print('new node written to nodelist.csv.')
                return 1
        except Exception as ex: #쓰기 실패시 에러 코드 출력 및 0을 리턴 값을 반환
            print(ex)
            return 0

def readNodes(filePath): #노드리스트 읽기 함수 정의
    print("read Nodes") #먼저 읽어온다는 안내문구 출력 후 빈 배열 설정
    importedNodes = []

    try: #읽기모드로 파일 열기
        with open(filePath, 'r',  newline='') as file:
            txReader = csv.reader(file)
            for row in txReader: #읽어온 파일을 한 행씩 가지고오기
                line = [row[0],row[1]] #라인 변수에 행의 0,1번쨰 인덱스 담아주기 (ip, port)
                importedNodes.append(line) #빈 배열에 라인에 담긴 값 추가하기
        print("Pulling txData from csv...") #파일에서 데이터 가지고 오고있다는 안내문구 출력
        return importedNodes #노드 정보가 담긴 리스트 리턴
    except: #읽어오기 실패시 빈 배열 리턴
        return []

def broadcastNewBlock(blockchain): #새로은 블록 브로드캐스트 해주는 함수
    #newBlock  = getLatestBlock(blockchain) # get the latest block
    importedNodes = readNodes(g_nodelstFileName) #노드리스트에서 파일 읽어오기(readNode 함수에서 노드 정보가 들어있는 배열을 리턴해 줄 것이다)  # get server node ip and port
    reqHeader = {'Content-Type': 'application/json; charset=utf-8'} #헤더값 정의
    reqBody = [] #바디는 빈 배열로
    for i in blockchain: #블록채인의 블록들 하나씩 가지고옴
        reqBody.append(i.__dict__) #블록을 딕셔너리 형태로 변환 후 바디에 추가해줌

    if len(importedNodes) > 0 : #노드 리스트에 노드 정보가 존재할 경우
        for node in importedNodes: #노드리스트의 노드들을 하나씩 가지고옴
            try: #URL 에 노드리스트에서 가지고 온 노드의 ip, port 값을 추가해줌. / g_receiveNewBlock = "/node/receiveNewBlock"
                URL = "http://" + node[0] + ":" + node[1] + g_receiveNewBlock  # http://ip:port/node/receiveNewBlock
                res = requests.post(URL, headers=reqHeader, data=json.dumps(reqBody)) #포스트 방식으로 리퀘스트 날리기 (헤더에는 위에서 정의한 헤더정보 / 데이타에는 딕셔너리 형식으로 되어있는 블록체인 정보를 제이슨 형식으로 변환한 것 ) / 리퉤스트에 대한 결과값을 res변수에 저장
                if res.status_code == 200: #URL 이 정상적으로 리퀘스트가 갔을 경우 만약 리스폰스 코드가 200이라면
                    print(URL + " sent ok.") # 정상적으로 정송되었다는 안내문구 출력
                    print("Response Message " + res.text) #리스폰스 내용 출력 ( .text로 리스폰스의내용 가지고오기)
                else: #200이 아니라면
                    print(URL + " responding error " + res.status_code) #에러 문구 + 리스폰스 코드 출력
            except: #리퀘스트 전송에 실패한 경우
                print(URL + " is not responding.") #유알엘이 응답하지 않는다는 안내문구 출력
                # write responding results
                tempfile = NamedTemporaryFile(mode='w', newline='', delete=False) #임시파일 생성
                try: #노드리스트 파일 읽어와 reader에는 csv파일을 읽어오고 writer에는 임시파일을 작성한다.
                    with open(g_nodelstFileName, 'r', newline='') as csvfile, tempfile:
                        reader = csv.reader(csvfile)
                        writer = csv.writer(tempfile)
                        for row in reader: #읽어온 노드리스트 파일을 한 행씩 가지고오기
                            if row: #행이 존재할경우
                                if row[0] == node[0] and row[1] ==node[1]: #만약 파일에서 읽어온 노드정보와 우리가 전송하려는 노드정보가 같을 경우
                                    print("connection failed "+row[0]+":"+row[1]+", number of fail "+row[2]) #노드리스트에는 정상적으로 존재하는 노드인데 리퀘스트를 날리는 데 실패함 그렇다면?
                                    tmp = row[2] #연결 실패 안내문구 출력 + 노드리스트 2번 인덱스 값을 변수에 담아줌
                                    # too much fail, delete node
                                    if int(tmp) > g_maximumTry: # 위의 조건을 만족하면서 노드[2] 값이 최대 시도 횟수보다 클 경우
                                        print(row[0]+":"+row[1]+" deleted from node list because of exceeding the request limit") #노드정보 + 최대 시도 횟수를 초과해 노드 정보를 삭제한다는 안내문구 출력
                                    else: #최대시도횟수를 초과하지 않을 경우
                                        row[2] = int(tmp) + 1 # 값을 1 증가해줌
                                        writer.writerow(row) #임시파일에 업데이트된 행을 작성
                                else: #파일에서 읽어온 노드 정보와 우리가 전송하려는 노드 정보가 같지 않을 경우
                                    writer.writerow(row) #임시파일에 노드 정보를 추가해줌
                    shutil.move(tempfile.name, g_nodelstFileName) #기존 노드정보 파일 덮어쓰기
                    csvfile.close() #파일 당아주기
                    tempfile.close()
                except: #읽기 혹은 작성에 실패한 경우 예외 안내문구 출력
                    print("caught exception while updating node list")

def row_count(filename): # 행수를 세어보자
    try: #파일 열기
        with open(filename) as in_file:
            return sum(1 for _ in in_file)
    except:
        return 0

#어떤게 최신 블록인지 확인하기위해 호출한다.
#파일로 작성되어있는 블록과 데이터로 들어온 것을 비교해서 더 최신의 파일을 확인한다.
def compareMerge(bcDict): #비교 병합 함수 딕셔너리 형태의 파일을 파라미터로 받아온다.

    heldBlock = [] #빈 배열 선언
    bcToValidateForBlock = []

    # Read GenesisBlock
    #스텝 1
    #1-1
    # 블록체인 파일을 읽기모드로 열어주로 포문을 돌며 csv파일의 한 행을 가지고와 그 요소들을 블록 클래스에 파라미터로 넣어준다. 그리고 생성한 블록을 heldBlock변수에 넣어준다.
    #이 과정을 실패하면 -1을 리턴하게된다.
    #위의 과정을 끝낸 뒤 heldBlock의 길이가 0이라면, 다시 -2리턴
    #1 -2
    #포문을 돌며 파라미터로 들어온 딕셔너리 형태의 변수에서 요소를 하나씩 꺼내와 블록 클래스에 넣어준다. 파라미터로 받아온 블록은 bc리스트에 넣어준다.
    #만들어진 두 리스트의 제네시스 블록(0번째 블록)이 같은 블록이 아니라면 -1을 리턴한다.
    try: #블록체인 파일 읽기모드로 열기
        with open(g_bcFileName, 'r',  newline='') as file:
            blockReader = csv.reader(file) #연 파일을 블록 리더라는 변수에 할당
            #last_line_number = row_count(g_bcFileName)
            for line in blockReader: #담아둔 파일을 한줄씩 읽어오기
                block = Block(line[0], line[1], line[2], line[3], line[4], line[5]) #블록 클래스 호출 / 파라미터로 읽어온 라인의 요소들을 넣어주기
                heldBlock.append(block) #생성해둔 빈 배열에 블록 추가

    except: #위의 과정 실패 시 안내문구 출력 후 -1 리턴
        print("file open error in compareMerge or No database exists")
        print("call initSvr if this server has just installed")
        return -1

    if len(heldBlock) == 0 : #만약 배열의 길이가 0이라면 = 아무것도 들어있지 않다면
        print("fail to read") #읽어오는데 실패했다는 문구 출력 후 -2 리턴
        return -2

    # transform given data to Block object
    for line in bcDict: #파라미터로 받아온 변수에서 한 요소씩 꺼내오기
        # print(type(line))
        # index, previousHash, timestamp, data, currentHash, proof
        block = Block(line['index'], line['previousHash'], line['timestamp'], line['data'], line['currentHash'], line['proof']) #그 요소의 키값으로 벨류를 가지고온다 / 그 결과를 블록 클래스에 할당
        bcToValidateForBlock.append(block) #위에서 정의해둔 빈 배열에 정의한 블록 넣기

    # compare the given data with genesisBlock
    if not isSameBlock(bcToValidateForBlock[0], heldBlock[0]): #같은 블록인지 검증하는 함수 호출 / 만약 같지 않다면 제네시스 블록이 일치하지 않는다는 문구 출력
        print('Genesis Block Incorrect')
        return -1 #-1 리턴

    # check if broadcasted new block,1 ahead than > last held block
    #스텝 2
    #만약 파라미터로 받아온 블록의 마지막과 csv로 읽어온 블록의 마지막을 파라미터로 주고 유효성 검증 함수를 호출하였을 때 그 값이 거짓이라면, (블록 검증은 (지금블록 , 이전블록) 을 파라미터로 받는다)
        #2-1
        #만약 두 파라미터가 유효하지 않다는 조건을 만족하면서 is same블록이라는 함수를 호출하였을 때 같은 블록이라면 ? (같은 블록이라면 당연히 위에서는 거짓 값이 반환됬을 것이다 . 검증 함수는 현재블록과 이전블록을 비교하는 함수니까)
        #이미 브로드캐스트되어 업데이트 되었다는 안내를 출력한 뒤 2를 리턴한다.

    if isValidNewBlock(bcToValidateForBlock[-1],heldBlock[-1]) == False: #블록이 유효한지 확인하는 함수 호출 ( 만들어 둔 리스트의 각각 마지막 행을 파라미터로 넣어줌 ) 그 결과가 거짓이라면,

        # latest block == broadcasted last block
        if isSameBlock(heldBlock[-1], bcToValidateForBlock[-1]) == True: #첫번 째 조건을 만족했을 때 같은 블록인지 검증하는 블록 (마찬가지로 리스트의 각각 마지막 행을 넣어줌) 그 결과가 참이라면,
            print('latest block == broadcasted last block, already updated')
            return 2 # 마지막블록은 이미 브로드캐스트되어 업데이트 되었다는 안내문구를 출력 후 2를 리턴함
        # select longest chain

        #2-2
    #만약 파라미터로 받아온 블록의 마지막과 csv로 읽어온 블록의 마지막을 파라미터로 주고 유효성 검증 함수를 호출하였을 때 그 값이 거짓이면서
        #파라미터로 받온 블록이 블록체인 csv파일보다 긴경우 :
            #만약 두 블록체인의 0번째가 같지 않다면 -1을 리턴 ,
            #포문을 돌며 파라미터 블록을 하나씩 꺼내옴
                #꺼내온 요소와 파라마터 블록의 i번째의 [i-1]번째 요소를 검증 함수에 넣고 만약 그 값이 참이라면, temp블록에 파라미터 블록의 i번째를 추가 / 유효하지 않은 경우에는 -1 리턴
            #빈배열 설정 / 파라미터 블록과 csv블록의 길이 차이 구하기
            #파라미터 블록의 [-차이] 부터 끝까지 포문을 돌며 블록 하나씩 꺼내오기
                #블록리스트는 파라미터블록에서 꺼내온 블록의 요소들을 저장, 빈 블록체인 리스트에 블록 추가해주기
            #파일을 추가모드로 열어서 차이 : 끝까지의 블록을 csv파일에 추가해줌
            #1리턴

        elif len(bcToValidateForBlock) > len(heldBlock): #첫번 째 조건을 만족하면서 bcToValidateForBlock의 길이가 heldBlock보다 긴 경우 (갯수가 더 많은 경우)
            # validation
            if isSameBlock(heldBlock[0],bcToValidateForBlock[0]) == False: #만약 csv파일의 0번째와 파라미터로 받아온 파일의 0번째가 같지 않은 경우
                    print("Block Information Incorrect #1")
                    return -1 #블록정보가 일치하지 않는다는 안내문구 출력 후 -1 리턴
            tempBlocks = [bcToValidateForBlock[0]] #임시블록 변수에 파라미터로 받아온 블록의 0번째를 넣어줌
            for i in range(1, len(bcToValidateForBlock)): #파라미터로 받아온 블록의 길이만큼 포문 돌기 (1부터 시작 0은 템프블록에 들어있음)
                if isValidNewBlock(bcToValidateForBlock[i], tempBlocks[i - 1]): #유효성 검증 함수 호출 시 유효한경우(파라미터로 들어온 블록의 i번째와 임시 블록의
                    tempBlocks.append(bcToValidateForBlock[i]) #템프블록에 파라미터로 들어온 블록의 i번째를 넣어줌
                else: #유효하지 않은 경우 -1 리턴
                    return -1
            # [START] save it to csv
            # TODO: append 정상여부 검증 필요
            blockchainList = [] #비어있는 블록체인 리스트 값 정의
            lengthGap = len(bcToValidateForBlock) - len(heldBlock)  # lenGap = 파라미터로 받은 블록과 csv로 읽어온 블록의 길이 차이
            for block in bcToValidateForBlock[-lengthGap:]: #파라미터로 받아온 블록의 [차이:끝]까지 -> 블록의 갯수가 3개 차이난다면 [-3:] 포문을 돌면서 블록을 하나씩 가지고옴
                blockList = [block.index, block.previousHash, str(block.timestamp), block.data, #블록 리스트 변수에 포문으로 가지고 온 블록의 요소들을 넢어줌
                             block.currentHash, block.proof]
                blockchainList.append(blockList)  # blockchainList에 타노드의 block을 list 형태로 담아줌
            with open(g_bcFileName, "a", newline='') as file: #블록 csv파일을 추가 모드로 열어준다.
                writer = csv.writer(file) #블록체인 씨에스비 파일에 포문으로 가지고 온 블록들을 넣어준다.
                writer.writerows(blockchainList)
            return 1
        #2-3
    # 만약 파라미터로 받아온 블록의 마지막과 csv로 읽어온 블록의 마지막을 파라미터로 주고 유효성 검증 함수를 호출하였을 때 그 값이 거짓이면서
        # 만약 bc블록보다 held블복의 길이가 더 길다면:
            #템프블록에 파람으로 들어온 블록의 0번째를 넣어줌
            #for문으로 검증함수에 (파람의 i번째 블록 , i-1블록(한개 이전 블록))을 넣어줌
                #만약 그 값이 참이라면, 파람블록[i]번째에 임시블록을 넣어줌
                #참이아니라면, -1리턴
            #더 긴 블록체이 있다는 안내문구 출력 후 3리턴

        elif len(bcToValidateForBlock) < len(heldBlock):
            # validation
            #for i in range(0,len(bcToValidateForBlock)):
            #    if isSameBlock(heldBlock[i], bcToValidateForBlock[i]) == False:
            #        print("Block Information Incorrect #1")
            #        return -1
            tempBlocks = [bcToValidateForBlock[0]]
            for i in range(1, len(bcToValidateForBlock)):
                if isValidNewBlock(bcToValidateForBlock[i], tempBlocks[i - 1]):
                    tempBlocks.append(bcToValidateForBlock[i])
                else:
                    return -1
            print("We have a longer chain")
            return 3
        #2-4
        #위의 조건들에 모두 걸리지 않는다면 블록 정보가 정확하지 않다는 안내문구 출력 후 -1 리턴
        else:
            print("Block Information Incorrect #2")
            return -1
    #스텝 3
    #만약 파라미터로 받아온 블록의 마지막과 csv로 읽어온 블록의 마지막을 파라미터로 주고 유효성 검증 함수를 호출하였을 때 그 값이 참 이라면:
        #3-1
        #템프블록에 파람블록의 0번을 넣어줌 (포문이 1번부터 돌면기 때문에 그 전 블록ㅇ니 0번 블록을 템프블록으로 잡아준 것이다 ) 포문이 돌아가면서 i-1번째 블록을 템프블록에 덮어쓰게된다.
        #포문을 돌면서 파람블록의 i번째와 템프블록 i-1 번째를 파라미터로 검증 함수를 호출 , 그 값이 참이라면 임시블록에 파람블록의 i번째를 추가해준다.(다음 블록 검증을 위해 현재 블록을 임시 변수에 넣어두는 것 )
        #만약 검증증 함수 호출 시 참이 아니라면 블록 정보가 맞지 않다는 안내문구 출력 후 템프 블록을 딕셔너리 형태로 반환해 출력해준다. 그리고 -1 리턴

    else: # very normal case (ex> we have index 100 and receive index 101 ...)
        tempBlocks = [bcToValidateForBlock[0]]
        #3-1 -> 파라미터로 받아온 블록체인에서 특정 블록과 그 전 블록을 검증하기. 검증에 실패하면 -1 리턴
        for i in range(1, len(bcToValidateForBlock)):
            if isValidNewBlock(bcToValidateForBlock[i], tempBlocks[i - 1]):
                tempBlocks.append(bcToValidateForBlock[i])
            else:
                print("Block Information Incorrect #2 "+tempBlocks.__dict__)
                return -1

        print("new block good")

        # 3-2
        # 포문을 돌며 0번째 블록부터 csv파일의 길이만큼 돌며 검증하기
        # 동일 블록 검사 함수에 csv,파람 블록의 각각 i번째를 같이 넣으줌이
        for i in range(0, len(heldBlock)): #만약 그 값이 거짓이라면? 블록 정보가 틀렸다는 안내문구 출력 후 -1 리턴
            if isSameBlock(heldBlock[i], bcToValidateForBlock[i]) == False:
                print("Block Information Incorrect #1")
                return -1
        # [START] save it to csv
        #3-3
        #빈배열 설정
        #포문으로 파라미터로 받아온 블록체인에서 블록 하나씩 꺼내오기
            #블록 리스트에 꺼내온 블록의 요소들 가지고와 그 값을 블록체인 리스트에 넣어준다
        #블록체인 파일을 쓰기 모드로 열고 완성된 블록체인 리스트 작성하기. 그리고 1리턴
        blockchainList = []
        for block in bcToValidateForBlock:
            blockList = [block.index, block.previousHash, str(block.timestamp), block.data, block.currentHash, block.proof]
            blockchainList.append(blockList)
        with open(g_bcFileName, "w", newline='') as file:
            writer = csv.writer(file)
            writer.writerows(blockchainList)
        # [END] save it to csv
        return 1

def initSvr(): #서버를 띄우고 1을 리턴해주는 함수
    print("init Server")
    #마지막라인넘버라는 함수에 노드파일의 행수를 세어 넣어준다
    last_line_number = row_count(g_nodelstFileName)
    #그 수가 0이라면, 딕셔너리 형태의 노드리스트에서 아이템을 하나씩 꺼나와 키와 밸류 값으로 나눠준다.
    if last_line_number == 0:
        for key, value in g_nodeList.items():
            URL = 'http://'+key+':'+value+'/node/getNode' #url에 가지고 온 키와 벨류값 넣어주고 노드 받아오기
            try: #위의 url로 리퀘스트를 보내고 그 결과를 리스폰스에 저장한다
                res = requests.get(URL)
            except requests.exceptions.ConnectionError: #에러 발생 시 컨디뉴 ( 아래는 모두 무시, 위로 올라가서 포문의 다음 번째 반복 시작한다)
                continue
            if res.status_code == 200 : #만약 받아온 리스폰스 결과가 200(성공)이라면, 리스폰스내용을 출력
                print(res.text) #제이슨 디코딩 -> 제이슨 형식의 리스폰스에서 내용 (텍스트)를 파이썬 형식으로 변환한다. 그 결과를 템프노드리스트에 담는다.
                tmpNodeLists = json.loads(res.text)
                for node in tmpNodeLists: #위에서 정의한 템프 노드 리스트에서 요소를 하나씩 가지고 와 addNode 함수에 파라미터로 넣어준다.
                    addNode(node)

    # 2. check if we have a blockchain data file
    #마지막 라인 넘버 = 블록체인 파일의 길이 /빈배열 선언
    last_line_number = row_count(g_bcFileName)
    blockchainList=[]
    if last_line_number == 0: #만약 그 값이 0 이라면, 블록체인 파일에 데이터가 없다면?
        # get Block Data...
        for key, value in g_nodeList.items(): #노드리스트의 각 항목에서 키와 벨류값을 꺼내온다
            URL = 'http://'+key+':'+value+'/block/getBlockData' #url에 노드리스트 정보 넣어주고 블록 데이터 받아오기 , getBlockData-> 블록데이터 리턴해줌. 리퀘스트가 들어오면 주소가 맞는지 확인(파싱) 하면 리드블록체인이 블록을 읽어 제이슨 형식의 값으로 보낸다.
            try: #위으 url로 리퀘스트보내고 그 결과를 리스폰스로 받아온다
                res = requests.get(URL) #에러 발생 시 컨티뉴
            except requests.exceptions.ConnectionError:
                continue
            if res.status_code == 200 : #만약 리스폰스 코드가 200이라면 리스폰스의 내용 출력
                print(res.text)
                tmpbcData = json.loads(res.text) #제이슨 디코딩 -> 문자열로 이루어진 제이슨 값을 파이썬 형식으로 바꿔주고 그 값을 변수에 넣어준다
                for line in tmpbcData: # 제이슨에서 받아온 값에서 한 라인씩 읽어오기 ( 겟 블록데이터 리퀘스트를 날렸으니까 리스폰스로는 무엇이 왔을까? )
                    # print(type(line))
                    # index, previousHash, timestamp, data, currentHash, proof
                    block = [line['index'], line['previousHash'], line['timestamp'], line['data'],line['currentHash'], line['proof']] #변수에 한줄씩 가지고 온 라인의 요소들 키값으로 가지고 오기
                    blockchainList.append(block) #블록체인리스트에 그 변수를 추가해준다.
                try: #블록체인 파일을 쓰기모드로 열어준다. 파일에 블록체인 리스트를 써준다.
                    with open(g_bcFileName, "w", newline='') as file:
                        writer = csv.writer(file)
                        writer.writerows(blockchainList)
                except Exception as e: #블록체인 파일 열기 실패 시 / 혹은 작성 실패시 에러 코드 출력
                    print("file write error in initSvr() "+e)

    return 1

# This class will handle any incoming request from a browser
class myHandler(BaseHTTPRequestHandler): #겟과 포스트 함수를 가지고 있는 클래스

    #def __init__(self, request, client_address, server):
    #BaseHTTPRequestHandler.__init__(self, request, client_address, server)
    #Handler for the GET requests

    def do_GET(self): #겟방식 함수 정의 -> 큰 경우의 수 3가지가 정의되어있다 받아온 path에 블록과 매칭되는 부분이 있는 경우 / 노드와 매칭되는 부분이 있는 경우 / 매칭되는 부분이 없는 경우 , 이 세가지 경우의 수 내부에서 더 상세하게 세부 매칭 여부를 확인하게된다.
        data = []  #빈 배열 설정 (리스폰스로 돌려줄 정보가 들어갈 아이) # response json data
        if None != re.search('/block/*', self.path): #엔드포인트 이 친구가 나오면 내부의 데이터들을 제이슨으로 덤핑한다. 정규표현식 -> *앞의 문자들이 0번이상 매칭되어야함. (파라미미터로 들어온 값.self)에 정규표현식에 매되는 부분이 있다면,
            if None != re.search('/block/getBlockData', self.path): #위의 정규표현식에 '/block/getBlockData'와 매칭되는 부분이 있으면서 아래의 정규표현식과 매칭된다면 (조금 더 디테일하게 찾아보는 컨셉!)
               # TODO : http://localhost:8666/block/getBlockData?from=1&end=10 -> from, end 문자열 검사
                try: #리스폰스를 보내기
                    self.send_response(200) #헤더의 컨텐트 타입에 애플리케이션 제이슨 넣어주기
                    self.send_header('Content-type', 'application/json') #헤더에는 어떤 방식으로 데이터를 표현할지에 대한 기본정보 (메타정보)가 들어간다.
                    self.end_headers() #헤더 닫기
                    block = readBlockchain(g_bcFileName, mode = 'external') #블록은 블록체인 파일을 readBlockCahing 함수로 읽어온 값
                    # 스마트금융 4기 김하나 미래산업기술동향 과제
                    # 총 6개의 예외를 정의해보았습니다.
                    # 1. 블록이 생성되지 않은경우
                    # 2. 쿼리문에 숫자가 아닌 문자가 들어온 경우
                    # 3. startpoint에 음수가 들어온 경우
                    # 4. startPoint가 블록의 길이보다 큰 경우
                    # 5. endPoint 값이 블록의 길이보다 길거나, 0보다 작을경우.
                    # 6. 한번에 조회하는 숫자가 100개보다 많을경우.

                    # 예외 1 : 블록이 생성되지 않았을 경우.
                    # 해결 1 : 블록이 존재하지 않는다는 안내문구 출력.
                    if block == None:
                        print("블록이 존재하지 않습니다.")
                        data.append("블록이 존재하지 않습니다.")
                    else:
                        # 예외 2 : 쿼리에 숫자가 아닌 문자가 들어온 경우
                        # 해결 2 : 일단 쿼리 형식이 올바른지 확인하기위해 int 형식으로 변환을 시도. 형식이 올바르지 않다면 except문으로 들어감.
                        try:
                            queryString = urlparse(self.path).query.split('&')
                            startPoint = int(queryString[0].split('=')[1]) - 1
                            endPoint = int(queryString[1].split('=')[1])

                            # 예외 3 : startPoint에 음수가 들어온 경우.
                            # 해결 3 : startPoint를 0으로 덮어씀.
                            if startPoint < 0  :
                                startPoint = 0

                            # 예외 4. startPoint가 블록의 길이보다 긴 경우
                            # 해결 4. 사용자에게 안내문구 출력 후 startPoint를 마지막 인덱스로 변경 (블록의 길이보다 더 큰 값을 넣었으니 넣을 수 있는 값중 가장 큰 값으로 바꿔줌)
                            if startPoint > len(block):
                                print("시작점이 잘못되었습니다. 설정할 수 있는 startPoint의 최대 범위는 {} 입니다. {} 번째 결과부터 조회합니다.".format((len(block) -1 ),(len(block) -1 )))
                                data.append("시작점이 잘못되었습니다. 설정할 수 있는 startPoint의 최대 범위는 {} 입니다. {} 번째 결과부터 조회합니다.".format((len(block) -1 ),(len(block) -1 )))
                                startPoint = len(block) -1

                            # 예외 5 : endPoint 값이 블록의 길이보다 길거나 0보다 작을경우.
                            # 아래에서 정의한 100이 넘어가는 예외 발생시 무조건 블록의 길이를 넘어가는 문제를 해결하기위해 블록의 길이보다 길고 endPoint - startPoint 가 100보다 작은 경우로 조건문을 작성했습니다.
                            # 해결 5-1 : 사용자에게 블록의 길이 알려줌.
                            # 해결 5 -2 : endPoint를 블록의 길이로 바꿔준다.
                            if (endPoint > len(block) and (endPoint - startPoint) < 100) or endPoint <= 0:
                                print("블록의 범위를 초과한 요청입니다. {} 개의 블록이 존재합니다.".format(len(block)))
                                data.append("블록의 범위를 초과한 요청입니다. {} 개의 블록이 존재합니다.".format(len(block)))
                                endPoint = len(block)

                            # 예외 6 : 한번에 조회하는 숫자가 100개보다 많을경우.
                            # 해결 6 : 리스트 분할 출력을 위한 for문
                            if (endPoint - startPoint) >= 100 : # 리스트 분할 출력을 위한 for문
                                start = startPoint # 인덱스 시작값을 startPoint로 잡아줌.
                                end = endPoint #인덱스의 마지막값을 endPoint로 잡아줌.
                                augmenter = 10 #한번에 출력할 값 정의 (여기서느 10으로 설정)
                                for i in range(start, end, augmenter):
                                    index = start + augmenter # 시작값 + 한번에 출력할 값
                                    printList = block[start:index] # 정의한 인덱스로 출력 범위 설정해 변수에 넣어줌
                                    if printList != []: # printList가 빈 리스트가 아니라면 if문 수행
                                        for element in printList: # printList의 element 하나씩 출력
                                            print(element.__dict__)
                                            data.append(element.__dict__)  # data에 element append
                                        start = index # 시작값을 마지막 인덱스 값으로 바꿔줌
                                        userInput = input("출력을 멈추시려면 엔터키를, 계속 출력을 원하시면 아무키나 입력하세요. ") # 사용자에게 계속 출력할지 선택. 사용자의 제약을 줄이기 위해 특정 문자가 아닌 아무 문자나 입력할 수 있게 처리.
                                        if len(userInput) > 0: # 사용자가 한글자라도 입력했다면 계속 수행
                                            continue
                                        else: # 아무것도 입력하지 않았으면 안내문구 출력 후 종료
                                            break
                                print("출력이 완료되었습니다.") #for 문이 끝나거나 break가 걸리면 안내문구 출

                            else : #출력해할 범위가 100보다 작은경우, 최종 startPoint와 endPoint를 이용해 for문.
                                for i in range(startPoint, endPoint):
                                    print(block[i].__dict__)
                                    data.append(block[i].__dict__)

                        except: #에외 1 해결 부분
                            print("잘못된 쿼리 형식입니다.")
                            data.append("잘못된 쿼리 형식입니다.")

                except: #위의 try문 실패 시 리스폰스를 500으로 전송
                    self.send_response(500) #헤더는 위와 똑같이 세팅해주고 데이터에 에러를 추가해주기
                    self.send_header('Content-type', 'application/json')
                    self.end_headers()
                    data.append("error")
                finally: #'/block/getBlockData'와 매칭하는 if 문의 최종 실행문
                    print("결과를 반환합니다.") #포스트맨으로 보내기 전 안내문구가 있으면 좋을 것 같아 추가해보았습니다.
                    self.wfile.write(bytes(json.dumps(data, sort_keys=True, indent=4), "utf-8")) #딕셔너리를 문자열로 -> html 작성 시 body 부분 , 실제 들어갈 내용을 넣는다 제이슨 인코딩 -> 위에 전송할 정보를 넣은 데이터 배열을 제이슨 형식으로 인코딩한다. 이부분이 있어 웹에 찍힐 수 있다.

            elif None != re.search('/block/generateBlock', self.path): #만약 처음 '/block/' 정규표현식에 매칭되면서 (첫번째 if문) , '/block/generateBlock'과 매칭되는 부분이 있다면?
                self.send_response(200) #리스폰스를 200으로 전송
                self.send_header('Content-type', 'application/json') #헤더에 필요한 정보 세팅해줌
                self.end_headers()
                #파이썬 프로그램은 기본적으로 하나의 스래(SingleThread)에서실행된다.즉, 하나의 메인 쓰레드가 파이썬 코드를 순차적으로 실행한다.
                #코드를 병렬로 실행하기 위해서는 별도쓰레드(Subthread)를 생성해야 하는데, 파이썬에서 쓰레드를 생성하기 위해서는 threading 모듈(High레벨) 혹은 thread 모듈(Low레벨)을 사용할 수 있다.
                #중국집 요리사와 , 배달부 느낌!
                t = threading.Thread(target=mine) #스레드에게 할일을 줬다. 할 일은 마이닝(채굴)을 하는 것!
                t.start() #스레드 스타트
                data.append("{mining is underway:check later by calling /block/getBlockData}") #데이터 배열에 문구를 추가해줌 "채굴이 진행중입니다. 나중에 다시 확인하세요~"
                self.wfile.write(bytes(json.dumps(data, sort_keys=True, indent=4), "utf-8")) #데이터 배열 제이슨 형태로 인코딩 해 웹에 찍기
            else: #정규표현식에 해당되지 않을 경우
                self.send_response(404) #리스폰스 코드 404 전송
                self.send_header('Content-type', 'application/json') #헤더 설정
                self.end_headers()
                data.append("{info:no such api}") # 데이터 배열에 문구 추가
                self.wfile.write(bytes(json.dumps(data, sort_keys=True, indent=4), "utf-8")) #제이슨 형식으로 인코딩해 웹에 띄우기

        elif None != re.search('/node/*', self.path): #첫번째 정규표현식 /block/ 와 매칭되지 않고 /node/와 매칭되는 부분이 있다면?

            if None != re.search('/node/addNode', self.path): #노드 추가 url -> /node/와 매칭되면서, '/node/addNode'와 매칭된다면?
                queryStr = urlparse(self.path).query.split(':') #쿼리스트링을 : 로 나눠 파싱하자
                print("client ip : "+self.client_address[0]+" query ip : "+queryStr[0]) #클라이언트 아이피와 쿼리에서 들어온 아이피 출력
                if self.client_address[0] != queryStr[0]: #만약 클라이언트 주소의[0]과 쿼리의[0]이 같지 않다면,
                    self.send_response(500) #500번대의 리스폰스를 보낸다
                    self.send_header('Content-type', 'application/json') #헤더설정
                    self.end_headers()
                    data.append("your ip address doesn't match with the requested parameter") #아이피가 맞지 않다는 안내문구 추가
                else: #만약 클라이언트 주소의[0]과 쿼리의[0]이 같다면,
                    try:
                        res = addNode(queryStr) #애드노드 함수를 호출 (받아온 쿼리스트링을 넣어준다) 파일에 존재하지 않는 새로운 노드라서 노드 추가 성공한다면 리턴 값으로 1이 올 것이다. 그 값을 리스폰스 변수에 넣어준다.
                    except: #에러 발생시 패스
                        pass
                    finally: #만약 클라이언트 주소의[0]과 쿼리의[0]이 같을 경우의 최종 실행문,
                        if res == 1: #만약 애드노드에서 온 리턴값이 1이라면,
                            self.send_response(200) #200 코드 전송
                            self.send_header('Content-type', 'application/json')
                            self.end_headers()
                            importedNodes = readNodes(g_nodelstFileName) #리드노드 함수(노트리스트 파일)를 호출했다. 노드리스트에 내용이 존재한다면 노드정보들이 담긴 리스트를, 존재하지 않는다면 빈 배열을 리턴 할 것이다. 그 값을 임포티드노드 배열에 담아준다.
                            data =importedNodes #잘 추가가 됐다면 리턴 값에 우리가 쿼리에서 받아온 노드 정보가 들어가 있을 것! 데이타 변수에 함수에서 받아온 노드 정보를 넣는다.
                            print("node added okay") #노드가 잘 추가되었다는 안내문구를 출력한다.
                        elif res == 0 : # 노드가 노드리스트에 이미 존재하지는 않지만, 노드 추가에 실패한 경우에 오는 리턴 값이다.
                            self.send_response(500) #그럴땐 500 코드를 보내준다
                            self.send_header('Content-type', 'application/json')
                            self.end_headers()
                            data.append("caught exception while saving") #저장 중에 예외가 생겼다는 안내문구 출력
                        elif res == -1 : # 이미 노드가 노드리스트에 존재한다는 리턴 값이다
                            self.send_response(500) #500의 리스폰스 주기
                            self.send_header('Content-type', 'application/json')
                            self.end_headers()
                            importedNodes = readNodes(g_nodelstFileName) #리드노드 함수(노트리스트 파일)를 호출했다. 노드리스트에 내용이 존재한다면 노드정보들이 담긴 리스트를, 존재하지 않는다면 빈 배열을 리턴 할 것이다. 그 값을 임포티드노드 배열에 담아준다.
                            data = importedNodes #데이터에 받아온 리턴값(배열)
                            data.append("requested node is already exists") # #요청한 노드가 이미 존재합니다 라는 안내 출력
                        self.wfile.write(bytes(json.dumps(data, sort_keys=True, indent=4), "utf-8")) #바디부분에 데이터 주기

            elif None != re.search('/node/getNode', self.path): #만약 node/와 매칭되면서, '/node/getNode'와 도 매칭된다면?
                try:
                    importedNodes = readNodes(g_nodelstFileName) #노드파일 읽어서 변수에 넣어주기 노드리스트에 내용이 존재한다면 노드정보들이 담긴 리스트를 반환해 줄 것이다
                    data = importedNodes #데이타에 읽어온 노드 정보들 넣어주기
                except: #에러 발생 시 데이터에 에러라는 문자열 넣어주기
                    data.append("error")
                    self.send_response(500) #500에러코드 전송
                    self.send_header('Content-type', 'application/json')
                    self.end_headers()
                else: #에러 발생하지 않을 시 ? 200 코드 전송
                    self.send_response(200)
                    self.send_header('Content-type', 'application/json')
                    self.end_headers()
                finally: #최종 실행문 -> 리드 노드 함수를 통해 받아온 노드 정보를 바디에 찍어준다.
                    self.wfile.write(bytes(json.dumps(data, sort_keys=True, indent=4), "utf-8"))

        else: # 매칭되는 정규표현식이 없다면?
                self.send_response(404) #제일싫어 404! 전송!
                self.send_header('Content-type', 'application/json')
                self.end_headers()

        # ref : https://mafayyaz.wordpress.com/2013/02/08/writing-simple-http-server-in-python-with-rest-and-json/
    def do_POST(self): #포스트 방식 함수-> 큰 경우의 수 3가지가 정의되어있다 받아온 path에 블록과 매칭되는 부분이 있는 경우 / 노드와 매칭되는 부분이 있는 경우 / 매칭되는 부분이 없는 경우 , 이 세가지 경우의 수 내부에서 더 상세하게 세부 매칭 여부를 확인하게된다.
        if None != re.search('/block/*', self.path): #정규표현식 사용 블록과 매칭되는 아이가 있다면?
            self.send_response(200) #200코드 전송
            self.send_header('Content-type', 'application/json')
            self.end_headers()

            if None != re.search('/block/validateBlock/*', self.path): #블록과 매칭되면서 '/block/validateBlock/*'과 매칭된다면?
                ctype, pdict = cgi.parse_header(self.headers['content-type']) #해더의 컨텐트 타입 부분을 파싱함. cgi-> 웹서버와 언어간의 쉬운 연동을 위한 표준화된 약속, 파싱한 결과물을 두개의 변수에 넣음 (키랑 밸류값을 넣음)
                #print(ctype) #print(pdict)

                if ctype == 'application/json': #만약 씨타입 변수가 어플리캐이션 제이슨이라면?
                    content_length = int(self.headers['Content-Length']) # content_length = 헤더에서 가지고온 content_length정보를 인트로 변환해 변수에 넣어준다.
                    post_data = self.rfile.read(content_length) #포스트 데이터 변수에 self.rfile을 출력해보면 <_io.BufferedReader name=10>가, self.rfile.read(content_length)를 모두 출력하면 바디에 들어있는 정보가 키/밸류 형태로 출력된다.
                    receivedData = post_data.decode('utf-8') #utf-8설정
                    print(type(receivedData)) #문자열 타입의 객체이다.
                    tempDict = json.loads(receivedData)  #문자열 타입의 객체를 리스트로 변환해준다. # load your str into a list /  print(type(tempDict))
                    if isValidChain(tempDict) == True : #체인 검증 함수 호출 -> 검증에 성공하면 리턴으로 참값을 줄것이다. 만약 검증에 성공했다면,
                        tempDict.append("validationResult:normal") #템프딕트 리스트에 "검증결과:정상" 값을 추가해준다.
                        self.wfile.write(bytes(json.dumps(tempDict), "utf-8")) #제이슨 덤프로 포스트맨의 바디에 찍어주기
                    else : #만약 검증에 실패했다면?
                        tempDict.append("validationResult:abnormal") #검증결과값으로 비정상을 넣어 리스트에 추가해준다
                        self.wfile.write(bytes(json.dumps(tempDict), "utf-8"))  #포스트맨으로 보내주기~ 바디에 찍어보자
            elif None != re.search('/block/newtx', self.path): #블록과 매칭되면서 트랜잭션과 매칭되는 부분이 있다면?
                ctype, pdict = cgi.parse_header(self.headers['content-type']) #헤더에서 컨탠트 타입 부분의 정보를 읽어오자
                if ctype == 'application/json': #만약 씨타입이 어플리케이션 제이슨이라면?
                    content_length = int(self.headers['Content-Length']) #컨텐트의 길이를 변수로 넣어줌
                    post_data = self.rfile.read(content_length) #포스트 데이터 변수에 self.rfile을 출력해보면 <_io.BufferedReader name=10>가, self.rfile.read(content_length)를 모두 출력하면 바디에 들어있는 정보가 키/밸류 형태로 출력된다.
                    receivedData = post_data.decode('utf-8') #문자열 형식의 변수
                    print(type(receivedData)) #문자열 값이 출력됨
                    tempDict = json.loads(receivedData) #템프 딕트를 출력하면 [{'sender': 'A', 'amount': '1000won', 'receiver': 'B'}] 이런식으로 출력된다 딕셔너리가 리스트 형식이 되어 출력
                    #print(tempDict)
                    res = newtx(tempDict) #새로운 트랜잭션을 만드는 함수에 가지고 온 리스트 형식의 파라미터를 넣어주고 그 결과를 리스폰스 변수에 넣어준다.
                    if  res == 1 : #뉴 티엑스 함수의 리턴 값이 1이라면,
                        tempDict.append("accepted : it will be mined later")
                        self.wfile.write(bytes(json.dumps(tempDict), "utf-8")) #바디에 찍어주기
                    elif res == -1 : #리턴값이 -1이라면? 트랜잭션의 갯수가 5개 이상이다
                        tempDict.append("declined : number of request txData exceeds limitation")
                        self.wfile.write(bytes(json.dumps(tempDict), "utf-8"))
                    elif res == -2 : #-2라면 트렌잭션 데이터가 0개이다. 데이터를 읽거나 쓰는데 에러 발생했다는 문구 추가
                        tempDict.append("declined : error on data read or write")
                        self.wfile.write(bytes(json.dumps(tempDict), "utf-8"))
                    else : #위의 경우들에 해당하지 않는다면 에러 메세지를 데이터에 추가하고 조건문 종료.
                        tempDict.append("error : requested data is abnormal")
                        self.wfile.write(bytes(json.dumps(tempDict), "utf-8"))

        elif None != re.search('/node/*', self.path): #정규표현식 사용 /node/ 과 매칭되는게 있다면??
            self.send_response(200) #리스폰스로 200을 줌
            self.send_header('Content-type', 'application/json') #헤더 세팅
            self.end_headers()
            if None != re.search(g_receiveNewBlock, self.path): # 노드와 매칭되면서  -> g_receiveNewBlock = /node/receiveNewBlock 과 매칭된다면?
                content_length = int(self.headers['Content-Length']) #헤더에서 가지고 온 컨텐트의 길이를 변수에 넣어줌
                post_data = self.rfile.read(content_length) #포스트 데이터 변수에 바디에 들어있는 정보가 키/밸류 형태로 저장한다.
                receivedData = post_data.decode('utf-8')
                tempDict = json.loads(receivedData) #tempDict = jason.loads - 제이슨 형태의 문자열을 파이썬 딕셔너리 형태로 변환해준다.  # load your str into a list
                print(tempDict)
                res = compareMerge(tempDict) #컴페어 머지 함수를 호출해 그 리턴값을 리스폰스에 넣어준다.
                if res == -1: #만약 블록이 유효하지 않다면 -1 이 리턴될 것이다
                    tempDict.append("internal server error")
                elif res == -2 : # 만약 들어온 파라미터의 길이가 0이라면? -2번이 리턴된다
                    tempDict.append("block chain info incorrect")
                elif res == 1: #성공했다면 리턴값으로 1 이 들어올 것이다 normal
                    tempDict.append("accepted")
                elif res == 2: #블록이 이미 브로드캐스트 되어 업데이트되었다면 2번이 오게된다. 그 결과를 타임디그에 추가해준다. identical
                    tempDict.append("already updated")
                elif res == 3: # 만약 파라미터로 넣은 체인보다 csv파일에서 읽어온 블록이 더 길다면 리턴값으로 3이 올 것.
                    tempDict.append("we have a longer chain")
                self.wfile.write(bytes(json.dumps(tempDict), "utf-8")) #바디에 제이슨 형식으로 찍어준다.
        else: #매칭되는 아이가 없다면? 너무 싫은 404를 리스폰스로 준다!
            self.send_response(404)
            self.send_header('Content-Type', 'application/json')
            self.end_headers()

        return #함수탈출

class ThreadedHTTPServer(ThreadingMixIn, HTTPServer): # ThreadingMixIn 비동기 동작을 지원 / HTTPServer 서버를 띄우기 위한 라이브러리
    """Handle requests in a separate thread."""

try:
    # Create a web server and define the handler to manage the
    # incoming request
    # server = HTTPServer(('', PORT_NUMBER), myHandler)
    server = ThreadedHTTPServer(('', PORT_NUMBER), myHandler) #서버의 https : // 'ip' ,'port' 이 라인으로 들어오는 요청은 마이핸들러가 처리하라고 명령하는 부분
    print('Started httpserver on port ', PORT_NUMBER)

    initSvr() #initSvr 함수 호출 만약 정상적으로 실행된다면 1을 리턴값으로 준다

    # Wait forever for incoming http requests
    server.serve_forever() # Ctrl - C 로 종료하기 전까지는 서버는 멈추지 않고 작동

except (KeyboardInterrupt, Exception) as e: #키보드 인터럽트 인셉션이 발생하면 컨트롤 + c가 입력되었고 웹 서버를 종료시킨다는 안내문구 출력
    print('^C received, shutting down the web server')
    print(e)
    server.socket.close() #서버 닫기